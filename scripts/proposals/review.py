#!/usr/bin/env python3
"""Require exact-head owner authorization for maintenance, and live-mode solves."""
import argparse
import json
from pathlib import Path
from check import require


def approved(reviews, owner, head):
    relevant = [r for r in reviews if r['user']['login'].lower() == owner.lower() and
                r['state'] in ('APPROVED','CHANGES_REQUESTED','DISMISSED')]
    latest = max(relevant, key=lambda r:r['id'], default=None)
    return bool(latest and latest['state']=='APPROVED' and latest['commit_id']==head)


def dispatched_approval(event, actor, triggering_actor, approved_head, owner, head):
    return (event == 'workflow_dispatch' and actor.lower() == owner.lower() and
            triggering_actor.lower() == owner.lower() and approved_head == head)


def requires_owner_review(mode, *, maintenance):
    require(mode in ('preview', 'live'), 'Invalid mode')
    return maintenance or mode == 'live'


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--reviews',type=Path,required=True); p.add_argument('--head',required=True)
    p.add_argument('--event',default=''); p.add_argument('--actor',default='')
    p.add_argument('--triggering-actor',default=''); p.add_argument('--approved-head',default='')
    p.add_argument('--maintenance',action='store_true',help='Require owner authorization even in preview mode')
    args=p.parse_args()
    policy=json.loads((Path(__file__).resolve().parents[2]/'.github/solve-policy.json').read_text())
    if not requires_owner_review(policy['mode'],maintenance=args.maintenance):
        print('Preview: checks are diagnostic; the owner makes the final merge decision.')
        return
    pages=json.loads(args.reviews.read_text())
    require(approved([r for page in pages for r in page],policy['owner'],args.head) or
            dispatched_approval(args.event,args.actor,args.triggering_actor,args.approved_head,policy['owner'],args.head),
            'The owner must authorize this exact commit by approving review or explicit workflow sign-off. New commits invalidate approval.')
    print('Owner approved this exact commit. Merge remains a manual owner action.')

if __name__=='__main__':main()
