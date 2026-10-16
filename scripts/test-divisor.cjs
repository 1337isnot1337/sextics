// Display-only polynomial evaluation and inverse projection.
const assert=require('node:assert/strict'),fs=require('node:fs'),path=require('node:path'),vm=require('node:vm');
const context={window:{},setTimeout};
vm.runInNewContext(fs.readFileSync(path.join(__dirname,'../assets/divisor.js'),'utf8'),context);
const {polynomial,ambient,apply}=context.HodgeDivisor;
const powers=(i,n)=>Array.from({length:6},(_,j)=>j===i?n:0);
assert.equal(polynomial([[2,powers(0,2)],[3,powers(3,2)]],[1,1,1,-1,-1,-1])([2,0,0,3,0,0]),-19);
assert.equal(polynomial([[1,powers(0,1)],[1,powers(3,1)]],[1,1,1,-1,1,1])([3,0,0,4,0,0]),5);
const meta={vertexCount:2,displayScale:2,centerOriginal:[1,0,0],planeMatrix:[[1,0,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,1],[0,0,0,0],[0,0,0,0]],phaseSigns:[1,1,1,1,1,1]};
const a=ambient([0,0,0],meta);
assert.deepEqual(Array.from(a),[1,0,0,0,0,0]);
(async()=>{
  const data=new Float32Array(18);data[9]=-.5;
  const mesh={buffer:data.buffer,meta};
  assert.equal(await apply(mesh,null),mesh);
  const shaded=await apply(mesh,[[1,powers(0,1)]]),result=new Float32Array(shaded.buffer);
  assert.ok(Math.abs(result[8]-Math.sqrt(2))<1e-6);assert.equal(result[17],0);
  assert.equal(data[8],0);assert.notEqual(shaded.buffer,mesh.buffer);
  await assert.rejects(()=>apply(mesh,[[1,powers(0,1)]],()=>false),/Cancelled/);
  console.log('Divisor display: real and complex phases, inverse projection, normalization, cancellation passed.');
})().catch(error=>{console.error(error);process.exitCode=1;});
