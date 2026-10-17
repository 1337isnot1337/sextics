/* Native GitHub conversations, loaded only when an instance's panel is opened. */
(()=>{
  'use strict';
  const escape=s=>String(s??'').replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
  const drafts=new Map();let current;
  const element=(tag,className,text)=>{const n=document.createElement(tag);n.className=className;if(text!==undefined)n.textContent=text;return n;};
  function link(text,url){const n=element('a','',text);try{const u=new URL(url);if(u.protocol!=='https:'||u.hostname!=='github.com')throw Error();n.href=u.href;n.target='_blank';n.rel='noopener noreferrer';}catch{}return n;}
  const button=(text,run)=>{const n=element('button','discussion-button',text);n.type='button';n.addEventListener('click',run);return n;};
  function markup(record){return `<section id="instanceDiscussion" class="discussion-panel" aria-labelledby="discussionHeading" data-instance="${escape(record.id)}" hidden>
    <header class="discussion-header"><div><p class="dialog-eyebrow">THE COMMON ROOM</p><h2 id="discussionHeading">Discussion <span class="discussion-count" hidden></span></h2></div><div class="discussion-tools"><a class="discussion-github" target="_blank" rel="noopener noreferrer" hidden>View on GitHub ↗</a><button type="button" class="discussion-refresh discussion-button" aria-label="Refresh discussion" aria-busy="false"><span>Refresh</span></button></div></header>
    <p class="discussion-context">${escape(record.title)} <span>·</span> Questions, calculations, and independent checks</p>
    <div class="discussion-notice" role="status" aria-live="polite"></div>
    <details class="discussion-intro" hidden><summary>About this thread</summary><div class="discussion-markdown"></div></details>
    <div class="discussion-feed" aria-label="Discussion for ${escape(record.title)}"></div>
    <button type="button" class="discussion-more discussion-button" hidden>Load more comments</button>
    <div class="discussion-access"></div>
    <form class="discussion-composer" hidden>
      <div class="discussion-reply-target" hidden><span></span><button type="button" class="discussion-cancel discussion-button">Cancel reply</button></div>
      <div class="discussion-editor-heading"><label for="discussionDraft">Add to the discussion</label><button class="discussion-preview-toggle discussion-button" type="button" aria-pressed="false">Preview</button></div>
      <textarea id="discussionDraft" rows="5" maxlength="30000" aria-describedby="discussionHelp" placeholder="Share an idea, calculation, or question…"></textarea>
      <div class="discussion-preview discussion-markdown" hidden></div>
      <div class="composer-footer"><span id="discussionHelp">Markdown and LaTeX: <code>$x^2$</code> inline, <code>$$…$$</code> on its own line.</span><button type="submit" class="discussion-submit">Post comment ↗</button></div>
      <p class="discussion-post-status" role="status" aria-live="polite"></p>
    </form>
  </section>`;}
  function mount(panel){
    current?.destroy();
    const id=panel.dataset.instance,endpoint='/api/discussions/'+encodeURIComponent(id),account=window.HodgeAccount;
    const q=s=>panel.querySelector(s),feed=q('.discussion-feed'),notice=q('.discussion-notice'),form=q('form'),draft=q('textarea'),preview=q('.discussion-preview'),submit=q('.discussion-submit'),refresh=q('.discussion-refresh');
    const requests=new AbortController(),comments=new Map(),expandedComments=new Map();let data=null,loaded=false,loading=false,posting=false,replyTo=null,previewing=false,version=0,commentSequence=0;
    const pendingKey='hodge-discussion-draft:'+id;
    let saved=drafts.get(id);try{saved||=JSON.parse(sessionStorage.getItem(pendingKey));}catch{}
    if(saved){draft.value=saved.body||'';replyTo=saved.replyTo||null;}
    const active=()=>panel.isConnected&&!requests.signal.aborted;
    function save(){const value={body:draft.value,replyTo};drafts.set(id,value);try{if(value.body)sessionStorage.setItem(pendingKey,JSON.stringify(value));else sessionStorage.removeItem(pendingKey);}catch{}}
    function rememberForSignIn(){save();try{sessionStorage.setItem('hodge-discussion-open',id);sessionStorage.setItem(pendingKey,JSON.stringify(drafts.get(id)));}catch{}account.signIn();}
    function setPreview(value){previewing=value;preview.hidden=!value;draft.hidden=value;q('.discussion-preview-toggle').textContent=value?'Write':'Preview';q('.discussion-preview-toggle').setAttribute('aria-pressed',String(value));if(value)HodgeDiscussionMarkdown.render(preview,draft.value||'*Nothing to preview yet.*');}
    function updateComposer(){
      form.hidden=!data?.viewerCanComment||!account.user;
      const access=q('.discussion-access');access.replaceChildren();
      if(data?.locked)access.textContent='This conversation is locked on GitHub.';
      else if(!account.user){access.append(element('span','','Join the conversation with your GitHub account.'),button('Sign in with GitHub ↗',rememberForSignIn));}
      else if(data){access.textContent='Posting as @'+account.user.login;}
      q('.discussion-reply-target').hidden=!replyTo;
      q('.discussion-reply-target span').textContent=replyTo?'Replying to @'+replyTo.login:'';
      q('label').textContent=replyTo?'Your reply':'Add to the discussion';
      submit.textContent=posting?'Posting…':replyTo?'Post reply ↗':'Post comment ↗';
      submit.disabled=posting||!draft.value.trim();draft.disabled=posting;q('.discussion-cancel').disabled=posting;
    }
    function message(text){notice.textContent=text;notice.hidden=!text;}
    function showPostStatus(text,url){const n=q('.discussion-post-status');n.textContent=text;if(url)n.append(' ',link('View on GitHub ↗',url));}
    function commentNode(comment,parent=null){
      const article=element('article','discussion-comment'+(parent?' discussion-reply':''));article.dataset.comment=comment.id;
      const header=element('header','discussion-comment-header'),author=comment.author;
      const identity=link(author?'@'+author.login:'Deleted account',author?.url);
      if(author?.avatarUrl){try{const u=new URL(author.avatarUrl);if(u.protocol==='https:'&&u.hostname==='avatars.githubusercontent.com'){const img=element('img','discussion-avatar');img.src=u.href;img.alt='';img.width=30;img.height=30;img.loading='lazy';img.referrerPolicy='no-referrer';identity.prepend(img);}}catch{}}
      const date=new Date(comment.createdAt),dateLink=link(Number.isNaN(+date)?'View comment':date.toLocaleDateString(undefined,{month:'short',day:'numeric',year:'numeric'}),comment.url);
      if(!Number.isNaN(+date))dateLink.title=date.toLocaleString();header.append(identity,dateLink);
      if(comment.updatedAt!==comment.createdAt)header.append(element('span','discussion-edited','edited'));
      const content=element('div','discussion-comment-content');content.id='discussion-comment-content-'+(++commentSequence);
      const toggle=button('',()=>{expandedComments.set(comment.id,content.hidden);updateExpansion();});toggle.classList.add('discussion-comment-toggle');toggle.setAttribute('aria-controls',content.id);
      const toggleLabel=element('span','');toggle.append(toggleLabel);toggle.insertAdjacentHTML('beforeend','<svg viewBox="0 0 20 20" aria-hidden="true"><path d="m5 7 5 5 5-5"/></svg>');
      const replyCount=comment.replies?.totalCount||0;
      if(replyCount)header.append(element('span','discussion-reply-count',`${replyCount} ${replyCount===1?'reply':'replies'}`));
      header.append(toggle);article.append(header,content);
      if(!expandedComments.has(comment.id))expandedComments.set(comment.id,comment.isMinimized||((comment.body||'').length<=1200&&(comment.body||'').split('\n').length<=14));
      let rendered=false;
      function updateExpansion(){
        const expanded=expandedComments.get(comment.id);content.hidden=!expanded;article.classList.toggle('discussion-collapsed',!expanded);
        toggle.setAttribute('aria-expanded',String(expanded));toggle.setAttribute('aria-label',`${expanded?'Collapse':'Expand'} comment by ${author?'@'+author.login:'deleted account'}`);toggleLabel.textContent=expanded?'Collapse':'Expand';
        if(expanded&&!rendered){rendered=true;renderContent();}
      }
      function renderContent(){
        const body=element('div','discussion-markdown');
        if(comment.isMinimized)body.textContent='This comment was hidden by a GitHub moderator.';else HodgeDiscussionMarkdown.render(body,comment.body);content.append(body);
        if(data.viewerCanComment&&!comment.isMinimized){content.append(button('Reply',()=>{if(posting)return;replyTo={id:(parent||comment).id,login:(parent||comment).author?.login||'deleted account'};save();setPreview(false);updateComposer();draft.focus();}));}
        if(!parent){
          const replies=element('div','discussion-replies');content.append(replies);
          for(const reply of comment.replies?.nodes||[])replies.append(commentNode(reply,comment));
          if(comment.replies?.pageInfo?.hasNextPage){const more=button('Load more replies',async()=>{
            more.disabled=true;
            try{const page=await account.request(endpoint+'/replies?'+new URLSearchParams({commentId:comment.id,after:comment.replies.pageInfo.endCursor}),{signal:requests.signal});if(!active())return;
              const seen=new Set(comment.replies.nodes.map(r=>r.id));comment.replies.nodes.push(...page.nodes.filter(r=>!seen.has(r.id)));comment.replies.pageInfo=page.pageInfo;
              article.replaceWith(commentNode(comment));
            }catch(e){if(active()){message(e.message);more.disabled=false;}}
          });content.append(more);}
        }
      }
      updateExpansion();
      return article;
    }
    function renderFeed(){
      feed.replaceChildren();
      if(!comments.size){const empty=element('div','discussion-empty');empty.append(element('h3','','Start the conversation.'),element('p','','Share a question, a partial calculation, or an independent check.'));feed.append(empty);}
      else for(const comment of comments.values())feed.append(commentNode(comment));
      const count=q('.discussion-count');count.hidden=false;count.textContent=String(data.comments.totalCount);count.title='Top-level comments';
      q('.discussion-more').hidden=!data.comments.pageInfo.hasNextPage;
      const github=q('.discussion-github');github.href=data.url;github.hidden=false;
      const intro=q('.discussion-intro');intro.hidden=!data.body;if(data.body)HodgeDiscussionMarkdown.render(intro.querySelector('div'),data.body);
      updateComposer();
    }
    async function load(append=false){
      if(loading)return;loading=true;const run=++version;refresh.disabled=true;refresh.setAttribute('aria-busy',String(!append));refresh.setAttribute('aria-label',append?'Refresh discussion':'Refreshing discussion');q('.discussion-more').disabled=true;
      message(append?'Loading more comments…':loaded?'':'Loading discussion…');
      try{await account.ready;if(!active()||run!==version)return;const next=await account.request(endpoint+(append?'?'+new URLSearchParams({after:data.comments.pageInfo.endCursor}):''),{signal:requests.signal});if(!active()||run!==version)return;
        data=next;loaded=true;if(!append)comments.clear();for(const c of next.comments.nodes)comments.set(c.id,c);renderFeed();message('');
      }catch(e){if(active()&&run===version){message(e.message);if(e.status===401||e.status===403){data=null;comments.clear();feed.replaceChildren();q('.discussion-intro').hidden=true;q('.discussion-count').hidden=true;q('.discussion-more').hidden=true;}updateComposer();}}
      finally{if(run===version){loading=false;refresh.disabled=false;refresh.setAttribute('aria-busy','false');refresh.setAttribute('aria-label','Refresh discussion');q('.discussion-more').disabled=false;}}
    }
    draft.addEventListener('input',()=>{save();updateComposer();});
    q('.discussion-preview-toggle').addEventListener('click',()=>setPreview(!previewing));
    q('.discussion-cancel').addEventListener('click',()=>{replyTo=null;save();updateComposer();});
    q('.discussion-refresh').addEventListener('click',()=>load());
    q('.discussion-more').addEventListener('click',()=>load(true));
    form.addEventListener('submit',async event=>{
      event.preventDefault();if(posting||!draft.value.trim()||!data?.viewerCanComment)return;
      posting=true;updateComposer();showPostStatus('');const parent=replyTo?.id,body=draft.value,postingUser=account.user?.login;
      try{const posted=await account.request(endpoint,{method:'POST',body:JSON.stringify({body,...(parent?{replyToId:parent}:{})})});
        drafts.delete(id);try{sessionStorage.removeItem(pendingKey);}catch{}if(!active()||account.user?.login!==postingUser)return;
        draft.value='';replyTo=null;setPreview(false);showPostStatus(parent?'Reply posted.':'Comment posted.',posted.url);
        expandedComments.set(posted.id,true);if(parent)expandedComments.set(parent,true);
        if(parent&&comments.has(parent)){const c=comments.get(parent);c.replies ||= {nodes:[],totalCount:0,pageInfo:{hasNextPage:false}};c.replies.nodes.push(posted);c.replies.totalCount++;}
        else if(!parent){comments.set(posted.id,{...posted,replies:{nodes:[],totalCount:0,pageInfo:{hasNextPage:false}}});data.comments.totalCount++;}
        renderFeed();
      }catch(e){if(active()){showPostStatus(e.status&&e.status<500?e.message:'Posting could not be confirmed. Your draft is saved; check the GitHub thread before trying again.',e.status&&e.status<500?null:data.url);if(e.status===401)await account.refresh();}}
      finally{posting=false;if(active())updateComposer();}
    });
    function sessionChanged(){if(!active())return;version++;loading=false;data=null;loaded=false;comments.clear();feed.replaceChildren();q('.discussion-intro').hidden=true;q('.discussion-intro div').replaceChildren();q('.discussion-github').hidden=true;q('.discussion-count').hidden=true;q('.discussion-more').hidden=true;updateComposer();if(!panel.hidden)load();}
    document.addEventListener('hodge-session-change',sessionChanged);
    const controller={open(){if(!loaded)load();},destroy(){save();requests.abort();document.removeEventListener('hodge-session-change',sessionChanged);}};
    try{controller.resume=sessionStorage.getItem('hodge-discussion-open')===id;if(controller.resume)sessionStorage.removeItem('hodge-discussion-open');}catch{}
    current=controller;updateComposer();return controller;
  }
  window.HodgeDiscussion={markup,mount};
})();
