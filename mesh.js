'use strict';
// Dependency-free watertight ramp meshing, binary STL and uncompressed ZIP.
const CurbMesh=(()=>{
function build(m,part){
 const N=part.b-part.a+1,K=m.st.mode==='hairpin'?Math.round(84*((part.t1??1)-(part.t0||0))):28,C=K+1,V=N*C,height=+m.st.height,lip=0.8;
 const p0=m.p[part.a],p1=m.p[part.b],angle=m.st.mode==='hairpin'?Math.PI/2:Math.atan2(p1.y-p0.y,p1.x-p0.x),cos=Math.cos(angle),sin=Math.sin(angle);
 let vertices=[],faces=[];
 for(let layer=0;layer<2;layer++)for(let i=0;i<N;i++){let p=m.p[part.a+i],q=m.outer[part.a+i];for(let j=0;j<=K;j++){let t=(part.t0||0)+(j/K)*((part.t1??1)-(part.t0||0)),x=p.x+(q.x-p.x)*t-p0.x,y=p.y+(q.y-p.y)*t-p0.y;let u=m.st.mode==='hairpin'?Math.abs(2*t-1):t;let shape=1-(m.blend?.[part.a+i]??1)*(3*u*u-2*u*u*u);vertices.push([x*cos+y*sin,-x*sin+y*cos,layer===0?lip+((m.crest?m.crest[part.a+i]:height)-lip)*shape:0]);}}
 const idx=(i,j)=>i*C+j;
 for(let i=0;i<N-1;i++)for(let j=0;j<K;j++){let a=idx(i,j),b=idx(i+1,j),c=idx(i+1,j+1),d=idx(i,j+1);const area=(u,v,w)=>{u=vertices[u];v=vertices[v];w=vertices[w];return Math.abs((v[0]-u[0])*(w[1]-u[1])-(v[1]-u[1])*(w[0]-u[0]));};if(Math.min(area(a,b,c),area(a,c,d))<1e-9){faces.push([a,b,d],[b,c,d],[a+V,d+V,b+V],[b+V,d+V,c+V]);}else faces.push([a,b,c],[a,c,d],[a+V,c+V,b+V],[a+V,d+V,c+V]);}
 let border=[];for(let i=0;i<N;i++)border.push(idx(i,0));for(let j=1;j<=K;j++)border.push(idx(N-1,j));for(let i=N-2;i>=0;i--)border.push(idx(i,K));for(let j=K-1;j>0;j--)border.push(idx(0,j));
 for(let i=0;i<border.length;i++){let a=border[i],b=border[(i+1)%border.length];faces.push([a,a+V,b+V],[a,b+V,b]);}
 let minX=Math.min(...vertices.map(v=>v[0])),minY=Math.min(...vertices.map(v=>v[1]));for(let v of vertices){v[0]-=minX;v[1]-=minY;}
 let targets=[],holePositions=[];
 const localTarget=(x,y)=>{let dx=x-p0.x,dy=y-p0.y;return[dx*cos+dy*sin-minX,-dx*sin+dy*cos-minY,+m.st.barrierH];};
 if(m.st.mode==='hairpin'&&part.a===0)targets.push(localTarget(0,+m.st.neckLen/2));
 if(m.st.mode==='curve'){
 const centerAtEnd=front=>{let i=front?0:m.p.length-1,j=front?1:i-1,p=m.p[i],q=m.outer[i],next=m.p[j],len=Math.hypot(next.x-p.x,next.y-p.y),d=+m.st.neckLen/2;return localTarget((p.x+q.x)/2+(next.x-p.x)/len*d,(p.y+q.y)/2+(next.y-p.y)/len*d);};
 if(part.a===0&&['both','start'].includes(m.st.transitions))targets.push(centerAtEnd(true));
 if(part.b===m.p.length-1&&['both','end'].includes(m.st.transitions))targets.push(centerAtEnd(false));
 }
 if(m.st.screws==='yes'){for(let target of targets.length?targets:[null]){faces=drill(vertices,faces,N,C,V,+m.st.headDia,+m.st.headDepth,part.id,target);holePositions.push({...vertices.hole});}}

 faces=orient(faces);let vol=volume(vertices,faces);if(vol<0){faces=faces.map(f=>[f[0],f[2],f[1]]);vol=-vol;}
 if(!Number.isFinite(vol)||vol<=0)throw Error('Ungültiges Volumen in Teil '+part.id);
 const holes=holePositions.map(hole=>({x:p0.x+cos*(hole.x+minX)-sin*(hole.y+minY),y:p0.y+sin*(hole.x+minX)+cos*(hole.y+minY),diameter:hole.diameter}));const mesh={vertices,faces,volume:vol,holes,hole:holes[0]||null};validate(mesh);return mesh;
}
function orient(faces){
 const edges=new Map,adj=faces.map(()=>[]);faces.forEach((f,i)=>f.forEach((a,k)=>{let b=f[(k+1)%3],key=Math.min(a,b)+':'+Math.max(a,b),old=edges.get(key);if(old){let same=old.a===a;adj[i].push([old.i,same]);adj[old.i].push([i,same]);}else edges.set(key,{a,i});}));
 let flags=new Map;for(let root=0;root<faces.length;root++){if(flags.has(root))continue;flags.set(root,false);let q=[root];while(q.length){let i=q.pop();for(let[j,same]of adj[i])if(!flags.has(j)){flags.set(j,flags.get(i)!==same);q.push(j);}}}return faces.map((f,i)=>flags.get(i)?[f[0],f[2],f[1]]:f);
}
function drill(v,faces,N,C,V,D,depth,id,target=null){
 if(!Number.isFinite(D)||D<6||D>20||!Number.isFinite(depth)||depth<1||depth>12)throw Error('Kopfvertiefung: Ø 6–20 mm, Tiefe 1–12 mm.');
 const R=D/2,margin=R+2,xy=(a,b)=>Math.hypot(a[0]-b[0],a[1]-b[1]);let best=null;
 let nearest=-1;if(target){let d=Infinity;for(let k=0;k<V;k++){let q=xy(v[k],target);if(q<d){d=q;nearest=k;}}}
 // Locate a rectangular surface patch with clearance to every part edge.
 for(let i=1;i<N-1;i++)for(let j=1;j<C-1;j++){
 if(target&&i*C+j!==nearest)continue;let c=target||v[i*C+j];if(c[2]<depth+2)continue;
 let a=i,b=i,l=j,r=j;while(a>0&&xy(c,v[a*C+j])<margin)a--;while(b<N-1&&xy(c,v[b*C+j])<margin)b++;while(l>0&&xy(c,v[i*C+l])<margin)l--;while(r<C-1&&xy(c,v[i*C+r])<margin)r++;
 if(a===0||b===N-1||l===0||r===C-1)continue;
 let border=[];for(let k=a;k<b;k++)border.push(k*C+l);for(let k=l;k<r;k++)border.push(b*C+k);for(let k=b;k>a;k--)border.push(k*C+r);for(let k=r;k>l;k--)border.push(a*C+k);
 let clearance=Infinity;for(let k=0;k<border.length;k++){let u=v[border[k]],w=v[border[(k+1)%border.length]],dx=w[0]-u[0],dy=w[1]-u[1],t=Math.max(0,Math.min(1,((c[0]-u[0])*dx+(c[1]-u[1])*dy)/(dx*dx+dy*dy)));clearance=Math.min(clearance,Math.hypot(c[0]-u[0]-t*dx,c[1]-u[1]-t*dy));}if(clearance<R+1)continue;
 let minZ=Math.min(...border.map(k=>v[k][2]));if(minZ-depth<2)continue;
 let score=minZ-0.001*Math.abs(i-(N-1)/2);if(!best||score>best.score)best={a,b,l,r,border,c,score,minZ};
 }
 if(!best&&target)throw Error('Teil '+id+': mittiges Schraubloch im Anschluss passt nicht. Anschluss-/Teilelänge erhöhen oder Kopfvertiefung verkleinern.');if(!best)throw Error('Teil '+id+': kein ausreichend dicker Bereich für das Schraubloch. Vertiefung verkleinern, Teilelänge erhöhen oder Befestigung ausschalten.');
 let{a,b,l,r,border,c,minZ}=best;v.hole={x:c[0],y:c[1],diameter:D};
 const inside=k=>{k%=V;let i=Math.floor(k/C),j=k%C;return i>=a&&i<=b&&j>=l&&j<=r;};
 let patch=faces.filter(f=>f.every(k=>k<V&&inside(k)));faces=faces.filter(f=>!f.every(k=>k<V&&inside(k))&&!f.every(k=>k>=V&&k<2*V&&inside(k)));
 function surface(x,y){for(let f of patch){let[A,B,Cc]=f.map(k=>v[k]),den=(B[1]-Cc[1])*(A[0]-Cc[0])+(Cc[0]-B[0])*(A[1]-Cc[1]);if(Math.abs(den)<1e-12)continue;let u=((B[1]-Cc[1])*(x-Cc[0])+(Cc[0]-B[0])*(y-Cc[1]))/den,w=((Cc[1]-A[1])*(x-Cc[0])+(A[0]-Cc[0])*(y-Cc[1]))/den;if(u>=-1e-6&&w>=-1e-6&&u+w<=1.000001)return u*A[2]+w*B[2]+(1-u-w)*Cc[2];}throw Error('Lochposition außerhalb der Fahrfläche.');}
 let rings=[[],[],[],[]],floor=minZ-depth;
 for(let k of border){let theta=Math.atan2(v[k][1]-c[1],v[k][0]-c[0]),cs=Math.cos(theta),sn=Math.sin(theta);for(let n=0;n<4;n++){let rad=n<2?R:2.5,x=c[0]+rad*cs,y=c[1]+rad*sn,z=n===0?surface(x,y):n===3?0:floor;rings[n].push(v.length);v.push([x,y,z]);}}
 const connect=(u,w)=>{for(let k=0;k<u.length;k++){let j=(k+1)%u.length;faces.push([u[k],u[j],w[j]],[u[k],w[j],w[k]]);}};
 connect(border,rings[0]);connect(rings[0],rings[1]);connect(rings[1],rings[2]);connect(rings[2],rings[3]);connect(rings[3],border.map(k=>k+V));return faces;
}
function normal(a,b,c){let u=b.map((v,i)=>v-a[i]),v=c.map((v,i)=>v-a[i]);return[u[1]*v[2]-u[2]*v[1],u[2]*v[0]-u[0]*v[2],u[0]*v[1]-u[1]*v[0]];}
function volume(v,f){let result=0;for(let [ia,ib,ic]of f){let a=v[ia],b=v[ib],c=v[ic];result+=(a[0]*(b[1]*c[2]-b[2]*c[1])+a[1]*(b[2]*c[0]-b[0]*c[2])+a[2]*(b[0]*c[1]-b[1]*c[0]))/6;}return result;}
function validate(mesh){let edges=new Map;for(let f of mesh.faces){let points=f.map(i=>mesh.vertices[i]);if(points.flat().some(n=>!Number.isFinite(n)))throw Error('Nicht endliche Koordinaten.');if(Math.hypot(...normal(...points))<1e-9)throw Error('Entartete Dreiecke. Bitte Messpunkte oder Breite korrigieren.');for(let i=0;i<3;i++){let a=f[i],b=f[(i+1)%3],key=Math.min(a,b)+':'+Math.max(a,b),e=edges.get(key)||[0,0];e[0]++;e[1]+=a<b?1:-1;edges.set(key,e);}}for(let [n,dir]of edges.values())if(n!==2||dir!==0)throw Error('Die Oberfläche ist nicht geschlossen.');return true;}
function stl(mesh){let bytes=new Uint8Array(84+mesh.faces.length*50),d=new DataView(bytes.buffer);bytes.set(new TextEncoder().encode('MSV Curb Planer | units: millimeters | flat base z=0'));d.setUint32(80,mesh.faces.length,true);let off=84;for(let face of mesh.faces){let points=face.map(i=>mesh.vertices[i]),n=normal(...points),len=Math.hypot(...n);for(let value of [...n.map(x=>x/len),...points.flat()]){d.setFloat32(off,value,true);off+=4;}d.setUint16(off,0,true);off+=2;}return bytes;}
const crcTable=Array.from({length:256},(_,n)=>{for(let k=0;k<8;k++)n=n&1?0xedb88320^(n>>>1):n>>>1;return n>>>0;});
function crc32(data){let c=0xffffffff;for(let b of data)c=crcTable[(c^b)&255]^(c>>>8);return(c^0xffffffff)>>>0;}
function zip(files){let local=[],central=[],offset=0;for(let f of files){let name=new TextEncoder().encode(f.name),data=typeof f.data==='string'?new TextEncoder().encode(f.data):f.data,crc=crc32(data);let h=new Uint8Array(30+name.length),v=new DataView(h.buffer);v.setUint32(0,0x04034b50,true);v.setUint16(4,20,true);v.setUint16(6,0x800,true);v.setUint16(12,33,true);v.setUint32(14,crc,true);v.setUint32(18,data.length,true);v.setUint32(22,data.length,true);v.setUint16(26,name.length,true);h.set(name,30);local.push(h,data);let ch=new Uint8Array(46+name.length),cv=new DataView(ch.buffer);cv.setUint32(0,0x02014b50,true);cv.setUint16(4,20,true);cv.setUint16(6,20,true);cv.setUint16(8,0x800,true);cv.setUint16(14,33,true);cv.setUint32(16,crc,true);cv.setUint32(20,data.length,true);cv.setUint32(24,data.length,true);cv.setUint16(28,name.length,true);cv.setUint32(42,offset,true);ch.set(name,46);central.push(ch);offset+=h.length+data.length;}
 let end=new Uint8Array(22),ev=new DataView(end.buffer),centralSize=central.reduce((a,b)=>a+b.length,0);ev.setUint32(0,0x06054b50,true);ev.setUint16(8,files.length,true);ev.setUint16(10,files.length,true);ev.setUint32(12,centralSize,true);ev.setUint32(16,offset,true);let out=new Uint8Array(offset+centralSize+22),pos=0;for(let a of [...local,...central,end]){out.set(a,pos);pos+=a.length;}return out;
}
return{build,validate,stl,zip,volume};})();
if(typeof module!=='undefined')module.exports=CurbMesh;
