import { randomBytes, createHash } from 'node:crypto';
import { Auth, cookies, equal, returnPath } from './auth.mjs';
import { ServiceError } from './github.mjs';

const random = () => randomBytes(32).toString('base64url');
const valid = value => typeof value === 'string' && /^[A-Za-z0-9_-]{43}$/.test(value);
const key = (type, value) => `${type}#${createHash('sha256').update(value).digest('hex')}`;

// All durable operations are delegated to a store shared by every invocation.
// Expiry is checked by the application; DynamoDB TTL is only eventual cleanup.
export class SharedAuth extends Auth {
  constructor(origin, store) { super(origin); this.store = store; }
  async start(returnTo) {
    const state = random(), binding = random(), verifier = random();
    await this.store.put(key('flow', state), { binding, verifier, returnTo:returnPath(returnTo), expires:Date.now()+600000 });
    return { state, challenge:createHash('sha256').update(verifier).digest('base64url'), cookie:this.cookie(this.flowName,binding,600) };
  }
  async finish(state, header) {
    if (!valid(state)) throw new ServiceError(400,'Sign-in could not be confirmed. Please try again.');
    const flow = await this.store.consume(key('flow',state));
    if (!flow || flow.expires <= Date.now() || !equal(flow.binding,cookies(header)[this.flowName])) throw new ServiceError(400,'Sign-in could not be confirmed. Please try again.');
    return flow;
  }
  async create(tokens,user) {
    const id=random(),seconds=Math.min(8*3600,Number(tokens.expires_in)||8*3600);
    if (seconds <= 0 || typeof tokens.access_token !== 'string') throw new ServiceError(401,'Please sign in again.');
    await this.store.put(key('session',id), { token:tokens.access_token,user,csrf:random(),expires:Date.now()+seconds*1000,lastPost:0 });
    return { id,cookies:[this.cookie(this.sessionName,id,seconds),this.cookie(this.flowName,'',0)] };
  }
  async get(header) {
    const id=cookies(header)[this.sessionName];
    if (!valid(id)) return null;
    const storageKey=key('session',id),session=await this.store.get(storageKey);
    return session && session.expires>Date.now() ? {...session,storageKey} : null;
  }
  async remove(header) {
    const id=cookies(header)[this.sessionName];
    if (valid(id)) await this.store.remove(key('session',id));
    return this.cookie(this.sessionName,'',0);
  }
  async claimPost(session) {
    if (!session?.storageKey || !await this.store.claimPost(session.storageKey,Date.now())) throw new ServiceError(429,'Please wait a few seconds before posting again.');
  }
}
