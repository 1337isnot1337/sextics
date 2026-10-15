// Accepted credit only, distinct instances, identity matching, ties; no network.
const assert=require('node:assert/strict'),fs=require('node:fs'),path=require('node:path'),vm=require('node:vm');
const root=path.join(__dirname,'..'),context={window:{}};
vm.runInNewContext(fs.readFileSync(path.join(root,'assets/leaderboard.js'),'utf8'),context);
const rank=(data,records)=>JSON.parse(JSON.stringify(context.window.HodgeLeaderboard.rank(data,records)));
const base={schemaVersion:2,basis:'accepted-proofs'};
const fixtures=['zoe','amy','amy','zoe','lee'].map((githubLogin,i)=>({id:String(i),status:'solved',certificateAvailable:true,formalStatus:'proved',credit:{githubLogin}}));
const credits=fixtures.map(r=>({instanceId:r.id,githubLogin:r.credit.githubLogin,origin:'contribution'}));
const data={...base,credits};
assert.deepEqual(rank(data,fixtures).map(r=>[r.githubLogin,r.rank,r.score,r.formalScore]),[['amy',1,2,2],['zoe',1,2,2],['lee',3,1,1]]);
assert.deepEqual(rank({...base,credits:[...credits,{...credits[0],githubLogin:'Zoe'}]},fixtures),rank(data,fixtures));
for(const changed of [{...credits[0],instanceId:'missing'},{...credits[0],githubLogin:'someone-else'},{...credits[0],githubLogin:'invalid/account'}])assert.throws(()=>rank({...base,credits:[changed]},fixtures));
for(const changed of [{formalStatus:'unproved'},{status:'open'},{certificateAvailable:false}])assert.throws(()=>rank({...base,credits:[credits[0]]},[{...fixtures[0],...changed}]));
assert.deepEqual(rank({...base,credits:[]},fixtures),[]);
const records=JSON.parse(fs.readFileSync(path.join(root,'data/index.json'))).records;
const live=JSON.parse(fs.readFileSync(path.join(root,'leaderboard/credits.json')));
assert.equal(rank(live,records).reduce((sum,r)=>sum+r.score,0),new Set(live.credits.map(c=>c.instanceId)).size);
console.log('Leaderboard: accepted credit, identity matching, distinct instances, ties, and current totals passed.');
