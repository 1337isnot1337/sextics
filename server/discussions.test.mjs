import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtemp, mkdir, writeFile, rm } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import path from 'node:path';
import { GitHub, readDiscussion, readReplies, postComment } from './github.mjs';
import { createService } from './server.mjs';
const entry={number:7,nodeId:'D_target'},session={token:'user-token'},repository='hodge-computer/sextics';
const leaf={id:'C_one',body:'$x^2$',url:'https://github.com/hodge-computer/sextics/discussions/7#discussioncomment-1',isMinimized:false};
const page=nodes=>({totalCount:nodes.length,nodes,pageInfo:{hasNextPage:false,endCursor:null}});
test('anonymous reads never expose a private repository; authenticated reads use the user token',async()=>{
 const github=new GitHub({repository});github.installationToken=async()=>'read-only-app';let privateRepo=true;
 github.call=async(p,{token})=>{assert.equal(p,'/repos/'+repository);assert.equal(token,'read-only-app');return {private:privateRepo};};
 await assert.rejects(github.readToken(null),e=>e.status===401);
 assert.equal(await github.readToken(session),'user-token');privateRepo=false;assert.equal(await github.readToken(null),'read-only-app');
});
test('reads bind the discussion ID, paginate and suppress minimized content at both levels',async()=>{
 const github={config:{repository},readToken:async()=>session.token,graphql:async(query,variables,token)=>{
  assert(!query.includes('viewerCanComment'));assert(query.includes('replies(first:20)'));assert.equal(variables.after,'cursor');assert.equal(token,session.token);
  return {repository:{discussion:{id:entry.nodeId,locked:false,comments:{...page([{...leaf,isMinimized:true,replies:page([{...leaf,id:'R',isMinimized:true}])}]),pageInfo:{hasNextPage:true,endCursor:'next'}}}}};
 }};
 const d=await readDiscussion(github,entry,'cursor',session);assert.equal(d.viewerCanComment,true);assert.equal(d.comments.pageInfo.endCursor,'next');assert.equal(d.comments.nodes[0].body,'');assert.equal(d.comments.nodes[0].replies.nodes[0].body,'');
 assert.equal((await readDiscussion(github,entry,'cursor',null)).viewerCanComment,false);
 await assert.rejects(readDiscussion(github,{...entry,nodeId:'wrong'},'cursor',session),e=>e.status===404);
});
test('reply pagination is restricted to a top-level comment of this instance',async()=>{
 let discussionId=entry.nodeId,replyTo=null;
 const github={readToken:async()=>session.token,graphql:async(query,vars,token)=>{assert.equal(vars.id,'C_one');assert.equal(vars.after,'next');assert.equal(token,session.token);return {node:{discussion:{id:discussionId},replyTo,replies:page([{...leaf,isMinimized:true}])}};}};
 assert.equal((await readReplies(github,entry,'C_one','next',session)).nodes[0].body,'');
 discussionId='D_other';await assert.rejects(readReplies(github,entry,'C_one','next',session),e=>e.status===404);
 discussionId=entry.nodeId;replyTo={id:'C_parent'};await assert.rejects(readReplies(github,entry,'C_one','next',session),e=>e.status===404);
});
test('posts use the authenticated user and reject cross-instance or nested reply targets',async()=>{
 let discussionId=entry.nodeId,replyTo=null;const mutations=[];
 const github={graphql:async(query,vars,token)=>{assert.equal(token,session.token);if(query.startsWith('mutation')){mutations.push(vars);return {addDiscussionComment:{comment:leaf}};}return {node:{discussion:{id:discussionId},replyTo}};}};
 await assert.rejects(postComment(github,entry,'body',null,null),e=>e.status===401);
 await postComment(github,entry,'body',undefined,session);assert.deepEqual(mutations[0],{input:{discussionId:entry.nodeId,body:'body'}});
 await postComment(github,entry,'reply','C_one',session);assert.equal(mutations[1].input.replyToId,'C_one');
 discussionId='D_other';await assert.rejects(postComment(github,entry,'reply','C_one',session),e=>e.status===400);
 discussionId=entry.nodeId;replyTo={id:'parent'};await assert.rejects(postComment(github,entry,'reply','C_one',session),e=>e.status===400);assert.equal(mutations.length,2);
});
test('HTTP boundary enforces target mapping, CSRF, body schema, pagination and rate limits',async()=>{
 const root=await mkdtemp(path.join(tmpdir(),'hodge-discussion-test-')),origin='https://test.example';let writes=0;
 await mkdir(path.join(root,'data'));await mkdir(path.join(root,'discussions'));
 await writeFile(path.join(root,'data/catalogue.json'),JSON.stringify({instanceIds:['holdout','unmapped']}));
 await writeFile(path.join(root,'discussions/index.json'),JSON.stringify({repository,instances:{holdout:entry}}));
 const github={config:{repository},readToken:async s=>s?.token||'public-token',graphql:async(query,vars,token)=>{
  if(query.startsWith('mutation')){writes++;assert.equal(token,'user-token');return {addDiscussionComment:{comment:leaf}};}
  if(vars.id)return {node:{discussion:{id:entry.nodeId},replyTo:null,replies:page([leaf])}};
  return {repository:{discussion:{id:entry.nodeId,url:'https://github.com/'+repository+'/discussions/7',locked:false,comments:page([leaf])}}};
 }};
 const service=await createService({root,origin,github});await new Promise(r=>service.server.listen(0,'127.0.0.1',r));const base='http://127.0.0.1:'+service.server.address().port;
 const created=service.auth.create({access_token:'user-token'},{login:'tester'}),cookie=created.cookies[0].split(';')[0],signed=service.auth.get(cookie);
 const headers={cookie,origin,'Content-Type':'application/json','X-CSRF-Token':signed.csrf};
 const post=(body,h=headers)=>fetch(base+'/api/discussions/holdout',{method:'POST',headers:h,body:JSON.stringify(body)});
 try{
  assert.equal((await fetch(base+'/api/discussions/missing')).status,404);assert.equal((await fetch(base+'/api/discussions/unmapped')).status,503);
  assert.equal((await post({body:'hello'},{})).status,401);assert.equal((await post({body:'hello'},{...headers,origin:'https://evil.test'})).status,403);
  for(const body of [{body:''},{body:'a'.repeat(30001)},{body:'hello',author:'someone-else'},{body:'hello',replyToId:5}])assert.equal((await post(body)).status,400);
  const read=await fetch(base+'/api/discussions/holdout');assert.equal(read.headers.get('cache-control'),'no-store');assert.equal((await read.json()).viewerCanComment,false);
  assert.equal((await fetch(base+'/api/discussions/holdout/replies?commentId=C_one')).status,200);assert.equal((await fetch(base+'/api/discussions/holdout/replies')).status,400);
  assert.equal((await post({body:'hello'})).status,201);assert.equal((await post({body:'again'})).status,429);assert.equal(writes,1);
 }finally{await new Promise(r=>service.server.close(r));await rm(root,{recursive:true,force:true});}
});
