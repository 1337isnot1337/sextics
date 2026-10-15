import { Readable } from 'node:stream';

// HTTP API payload v2 keeps Set-Cookie values separate, including on redirects.
export function bridge(handler) {
  return async event => {
    if(event.version!=='2.0'||!event.requestContext?.http) return {statusCode:400,body:'Invalid request.'};
    const bytes=Buffer.from(event.body||'',event.isBase64Encoded?'base64':'utf8');
    if(bytes.length>131072)return {statusCode:413,body:'The request is too long.'};
    const req=Readable.from(bytes.length?[bytes]:[]);
    req.method=event.requestContext.http.method;
    req.url=event.rawPath+(event.rawQueryString?'?'+event.rawQueryString:'');
    req.headers=Object.fromEntries(Object.entries(event.headers||{}).map(([k,v])=>[k.toLowerCase(),v]));
    if(event.cookies?.length)req.headers.cookie=event.cookies.join('; ');
    const result={statusCode:200,headers:{},cookies:[],body:''};
    const res={writeHead(status,headers){result.statusCode=status;for(const [key,value] of Object.entries(headers)){if(key.toLowerCase()==='set-cookie')result.cookies=Array.isArray(value)?value:[value];else result.headers[key]=String(value);}},end(body){result.body=body==null?'':String(body);}};
    await handler(req,res);
    return result;
  };
}
