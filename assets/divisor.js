/* Evaluate an accepted denominator on a saved real slice. Floating point is display only. */
(()=>{
'use strict';
function polynomial(terms,signs){
  const degree=Math.max(0,...terms.flatMap(([,powers])=>powers));
  const powers=Array.from({length:6},()=>new Float64Array(degree+1));
  const parts=[[],[]];
  for(const [coefficient,exponents] of terms){
    const phase=exponents.reduce((n,e,i)=>n+(signs[i]<0?e:0),0)%4;
    parts[phase%2].push([coefficient*(phase>=2?-1:1),exponents]);
  }
  const evaluate=list=>list.reduce((sum,[c,e])=>sum+c*e.reduce((product,n,i)=>product*powers[i][n],1),0);
  return coordinates=>{
    for(let i=0;i<6;i++){powers[i][0]=1;for(let j=1;j<=degree;j++)powers[i][j]=powers[i][j-1]*coordinates[i];}
    const real=evaluate(parts[0]),imag=evaluate(parts[1]);
    return parts[0].length&&parts[1].length?Math.hypot(real,imag):parts[0].length?real:imag;
  };
}
function ambient(position,meta){
  const [x,y,z]=position.map((v,i)=>v*meta.displayScale+meta.centerOriginal[i]);
  const r2=x*x+y*y+z*z,d=1+r2,u=[2*x/d,2*y/d,2*z/d,(r2-1)/d];
  return meta.planeMatrix.map(row=>row.reduce((sum,b,i)=>sum+b*u[i],0));
}
async function apply(mesh,terms,shouldContinue=()=>true){
  if(!terms?.length)return mesh;
  const {meta}=mesh,data=new Float32Array(mesh.buffer.slice(0));
  const evaluate=polynomial(terms,meta.phaseSigns),values=new Float64Array(meta.vertexCount);
  let sum2=0;
  for(let start=0;start<meta.vertexCount;start+=4096){
    if(!shouldContinue())throw new Error('Cancelled');
    for(let n=start;n<Math.min(meta.vertexCount,start+4096);n++){
      const offset=9*n,value=evaluate(ambient([data[offset],data[offset+1],data[offset+2]],meta));
      if(!Number.isFinite(value))throw new Error('Non-finite divisor sample.');
      values[n]=value;sum2+=value*value;
    }
    await new Promise(resolve=>setTimeout(resolve,0));
  }
  const scale=Math.max(1e-30,Math.sqrt(sum2/meta.vertexCount));
  for(let n=0;n<meta.vertexCount;n++)data[n*9+8]=values[n]/scale;
  return {...mesh,buffer:data.buffer,meta:{...meta,divisorScale:scale}};
}
globalThis.HodgeDivisor=Object.freeze({polynomial,ambient,apply});
})();
