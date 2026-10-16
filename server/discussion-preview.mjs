/* Disposable browser fixture. No credentials and no external API requests. */
import {mkdtemp,mkdir,cp,writeFile,rm,readFile} from 'node:fs/promises';
import {tmpdir} from 'node:os';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
import {createService} from './server.mjs';
import {ServiceError} from './github.mjs';
const source=path.resolve(path.dirname(fileURLToPath(import.meta.url)),'..');
const root=await mkdtemp(path.join(tmpdir(),'hodge-discussion-preview-')),origin='http://127.0.0.1:8773';
await mkdir(path.join(root,'assets'));await mkdir(path.join(root,'data'));await mkdir(path.join(root,'discussions'));
for(const name of ['vendor','favicon.svg','style.css','account.js','discussions.js','discussion-markdown.js'])await cp(path.join(source,'assets',name),path.join(root,'assets',name),{recursive:true});
await writeFile(path.join(root,'data/catalogue.json'),JSON.stringify({instanceIds:['holdout']}));
await writeFile(path.join(root,'discussions/index.json'),JSON.stringify({repository:'hodge-computer/sextics',instances:{holdout:{number:1,nodeId:'D_local'}}}));
const fixtures=[
 {id:'C_idea',body:'One possible approach is to start with **homogeneity**. If $D$ has degree $d$, we need $\\deg N_i = d + 6 \\cdot q - 5$.\n\n$$\nA \\cdot D^2 - q \\cdot D \\cdot \\sum_i N_i \\cdot \\partial_i F + F \\cdot (D \\cdot \\mathrm{div}(N) - \\sum_i N_i \\cdot \\partial_i D) = F^{q+1} \\cdot Q.\n$$\n\nThe quotient need not vanish. A non-strict certificate would be just as useful.',replies:{nodes:[{id:'R_1',body:'Agreed. I would also check the denominator condition \\(\\gcd(D,F)=1\\). Here is the exact code:\n\n```lean\nexample : 1 + 1 = 2 := by norm_num\n```'}],totalCount:2,pageInfo:{hasNextPage:true,endCursor:'reply-1'}}},
 {id:'C_hidden',body:'This must never be shown.',isMinimized:true},
 {id:'C_hostile',body:'Safety fixture: <img src=x onerror=alert(1)> [unsafe](javascript:alert(1))\n\n$\\href{javascript:alert(1)}{bad}$\n\n[Useful link](https://github.com/hodge-computer/sextics)'}
];
function decorate(c){return {url:origin+'/#comment-'+c.id,createdAt:'2026-10-15T14:00:00Z',updatedAt:'2026-10-15T14:00:00Z',isMinimized:false,author:{login:'example-contributor',url:'https://github.com/example-contributor'},...c,replies:c.replies?{...c.replies,nodes:c.replies.nodes.map(decorate)}:undefined};}
const comments=fixtures.map(decorate),page=(nodes,more=false,cursor=null)=>({nodes,totalCount:comments.length,pageInfo:{hasNextPage:more,endCursor:cursor}});let count=0;
const github={config:{repository:'hodge-computer/sextics'},readToken:async()=> 'local-token',graphql:async(query,vars)=>{
 if(query.startsWith('mutation')){if(vars.input.body==='SIMULATE_FAILURE')throw new ServiceError(502,'Simulated outage.');const c=decorate({id:'C_post_'+(++count),body:vars.input.body,author:{login:'local-tester',url:'https://github.com/local-tester'}});if(vars.input.replyToId){const parent=comments.find(c=>c.id===vars.input.replyToId);parent.replies||={nodes:[],totalCount:0,pageInfo:{hasNextPage:false}};parent.replies.nodes.push(c);parent.replies.totalCount++;}else comments.push(c);return {addDiscussionComment:{comment:c}};}
 if(vars.id)return {node:{discussion:{id:'D_local'},replyTo:null,replies:page([decorate({id:'R_2',body:'Additional reply loaded from the next page, with $q=2$.'})])}};
 return {repository:{discussion:{id:'D_local',number:1,title:'Holdout',body:'A shared mathematical conversation about the fixed target $(F,q,A)$.',url:'https://github.com/hodge-computer/sextics/discussions/1',locked:false,comments:vars.after?page(comments.slice(1)):page(comments.slice(0,1),true,'comments-1')}}};
}};
const service=await createService({root,origin,github});service.config.client_id='local-fixture';
const signed=service.auth.create({access_token:'local-token'},{login:'local-tester',name:'Local test account',url:'https://github.com/local-tester',avatar:'/assets/favicon.svg'});
// Use the actual page shell so nested scrolling and fixed controls are tested too.
for(const name of ['data','docs/technical','leaderboard'])await cp(path.join(source,name),path.join(root,name),{recursive:true});
for(const name of ['app.js','leaderboard.js'])await cp(path.join(source,'assets',name),path.join(root,'assets',name));
let html=await readFile(path.join(source,'index.html'),'utf8');
html=html.replace('<script defer src="assets/surface.js"></script>','<script>window.HodgeRenderer={create:()=>null};</script>').replace('<script defer src="assets/divisor.js"></script>','');
html=html.replace('ALGEBRAIC GEOMETRY <span>/</span> OPEN RESEARCH','LOCAL DISCUSSION TEST · NO MESSAGES LEAVE THIS COMPUTER');
await writeFile(path.join(root,'index.html'),html);
const handler=service.server.listeners('request')[0];service.server.removeAllListeners('request');service.server.on('request',(req,res)=>{
 if(req.url==='/'||req.url.startsWith('/?')){res.setHeader('Set-Cookie',req.url.includes('signedout')?'hodge_session=; Path=/; Max-Age=0':signed.cookies);}
 handler(req,res);
});
service.server.listen(8773,'127.0.0.1',()=>console.log('Local-only discussion fixture: '+origin));
async function close(){service.server.close();await rm(root,{recursive:true,force:true});process.exit(0);}process.on('SIGTERM',close);process.on('SIGINT',close);
