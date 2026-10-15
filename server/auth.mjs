import { randomBytes, createHash, timingSafeEqual } from 'node:crypto';
import { ServiceError } from './github.mjs';

const random = () => randomBytes(32).toString('base64url');
export function equal(a, b) {
  if (typeof a !== 'string' || typeof b !== 'string') return false;
  const left = Buffer.from(a), right = Buffer.from(b);
  return left.length === right.length && timingSafeEqual(left, right);
}
export function cookies(header = '') {
  return Object.fromEntries(header.split(';').map(s => s.trim().split('=')).filter(parts => parts.length === 2));
}
export function returnPath(value) {
  return typeof value === 'string' && /^\/#(?:home|technical-information(?:\/[a-z0-9-]+)?|leaderboard(?:\/[a-z0-9-]+)?|case\/[A-Za-z0-9-]+)?$/.test(value) ? value : '/#home';
}
export class Auth {
  constructor(origin) {
    this.origin = origin;
    this.secure = origin.startsWith('https:');
    this.sessions = new Map(); this.flows = new Map();
    this.sessionName = this.secure ? '__Host-hodge_session' : 'hodge_session';
    this.flowName = this.secure ? '__Host-hodge_oauth' : 'hodge_oauth';
  }
  cookie(name, value, maxAge) {
    return `${name}=${value}; Path=/; HttpOnly; SameSite=Lax; Max-Age=${maxAge}${this.secure ? '; Secure' : ''}`;
  }
  prune() {
    const now = Date.now();
    for (const map of [this.sessions, this.flows]) for (const [id, value] of map) if (value.expires <= now) map.delete(id);
  }
  start(returnTo) {
    this.prune();
    if (this.flows.size >= 1000) throw new ServiceError(429, 'Please try signing in again shortly.');
    const state = random(), binding = random(), verifier = random();
    this.flows.set(state, { binding, verifier, returnTo: returnPath(returnTo), expires: Date.now() + 600000 });
    return { state, challenge: createHash('sha256').update(verifier).digest('base64url'),
      cookie: this.cookie(this.flowName, binding, 600) };
  }
  finish(state, header) {
    this.prune();
    const flow = this.flows.get(state);
    this.flows.delete(state);
    if (!flow || !equal(flow.binding, cookies(header)[this.flowName])) throw new ServiceError(400, 'Sign-in could not be confirmed. Please try again.');
    return flow;
  }
  create(tokenResult, user) {
    this.prune();
    if (this.sessions.size >= 5000) throw new ServiceError(503, 'Please try signing in again shortly.');
    const id = random(), seconds = Math.min(8 * 3600, Number(tokenResult.expires_in) || 8 * 3600);
    this.sessions.set(id, { token: tokenResult.access_token, user, csrf: random(), expires: Date.now() + seconds * 1000, lastPost: 0 });
    return { id, cookies: [this.cookie(this.sessionName, id, seconds), this.cookie(this.flowName, '', 0)] };
  }
  get(header) { this.prune(); return this.sessions.get(cookies(header)[this.sessionName]) || null; }
  remove(header) { this.sessions.delete(cookies(header)[this.sessionName]); return this.cookie(this.sessionName, '', 0); }
  claimPost(session) {
    if (Date.now() - session.lastPost < 5000) throw new ServiceError(429, 'Please wait a few seconds before posting again.');
    session.lastPost = Date.now();
  }
  requireWrite(req, session) {
    if (!session) throw new ServiceError(401, 'Sign in with GitHub to post.');
    if (req.headers.origin !== this.origin || !equal(req.headers['x-csrf-token'], session.csrf)) throw new ServiceError(403, 'Please reload the page before posting.');
    if (!/^application\/json(?:;|$)/i.test(req.headers['content-type'] || '')) throw new ServiceError(415, 'Use JSON for this request.');
  }
}
