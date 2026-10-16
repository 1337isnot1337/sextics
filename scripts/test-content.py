#!/usr/bin/env python3
"""Test the content/acceptance boundary in disposable consistency fixtures.

Synthetic receipts below are not proof evidence and never enter the atlas.
The protected Lean runner and GitHub publisher are tested separately.
"""
import copy
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

import yaml

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'scripts/proposals'))
from acceptance import accepted_sources, solution_record, statement_hash

RID = 'test-example'

class ContentUpdates(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='hodge-content-test-')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        instance = {'id':RID, 'title':'Consistency fixture', 'q':1,
                    'F':'X0**6', 'A':'X0**5*Y0', 'formalStatus':'unproved',
                    'visibility':'visible', 'category':'fixture', 'rationale':'why.md',
                    'render':{}, 'polynomialData':{'F':{}, 'A':{}}}
        self.write(f'data/{RID}/instance.rec', yaml.safe_dump(instance))
        self.write(f'data/{RID}/why.md', 'A prospective reason.')
        self.write('data/catalogue.json', json.dumps({'schemaVersion':2,'instanceIds':[RID]}))
        self.write('docs/index.json', json.dumps({'schemaVersion':1,'pages':[],
            'overview':{'source':'docs/overview.md','content':'docs/overview.html'}}))
        self.write('docs/overview.md', r'An overview with \(F^{q+1}\).')
        self.write('leaderboard/accounts.json', '{"accounts": []}')
        self.write('index.html', '<main></main>')
        self.write('assets/renderer.js', '// Renderer fixture')
        self.run_build()

    def write(self, relative, text):
        path = self.root/relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def read(self, relative):
        return json.loads((self.root/relative).read_text())

    def run_build(self, success=True, check=False):
        result = subprocess.run([sys.executable,str(ROOT/'scripts/build-content.py'),'--root',str(self.root),
                                 *(['--check'] if check else [])], capture_output=True,text=True)
        self.assertEqual(result.returncode==0,success,result.stdout+result.stderr)
        return result

    def receipt_fixture(self, login='new-contributor'):
        folder=self.root/'data'/RID
        self.write(f'data/{RID}/proof.json',json.dumps({'schemaVersion':2,'instanceId':RID,
                   'theorem':'Submission.certificate','witnessTheorem':'Submission.witness'}))
        self.write(f'data/{RID}/Solution.lean','-- Content-binding fixture only, not a Lean proof.\n')
        self.write(f'data/{RID}/witness.json',json.dumps({'d':0,'D':'1/4','N':['0']*6,'Q':'0'}))
        self.write(f'data/{RID}/solution.md',r'An explanation with \(D=\frac14\).')
        instance=yaml.safe_load((folder/'instance.rec').read_text())
        pr={'number':123,'url':'https://github.com/hodge-computer/sextics/pull/123',
            'baseCommit':'a'*40,'headCommit':'b'*40,'mergeCommit':'c'*40}
        proof={'mode':'live','instanceId':RID,'kernelReplay':True,'result':'lean-checked-awaiting-owner',
               'axioms':['propext','Classical.choice','Quot.sound'],'verifierSha256':{'fixture':'d'*64},
               'sandbox':'docker-no-network','baseCommit':pr['baseCommit'],'headCommit':pr['headCommit'],
               'pullRequest':123,'githubLogin':login,'statementSha256':statement_hash(instance),
               'sourceHashes':accepted_sources(folder),'theorem':'Submission.certificate',
               'witnessChecked':True,'leanVersion':'consistency fixture'}
        receipt={'schemaVersion':1,'formalAcceptance':True,'repository':'hodge-computer/sextics',
                 'instanceId':RID,'verification':proof,'pullRequest':pr,'githubLogin':login,
                 'submittedAt':'2026-10-15T00:00:00Z','acceptedAt':'2026-10-15T00:01:00Z',
                 'run':{'workflowPath':'.github/workflows/solve-proposal.yml','id':123,'conclusion':'success'}}
        self.write(f'data/{RID}/acceptance.json',json.dumps(receipt))
        self.write(f'data/{RID}/solution.rec',yaml.safe_dump(solution_record(self.root,receipt)))
        return receipt

    def test_proof_files_alone_do_not_publish(self):
        self.receipt_fixture()
        (self.root/'data'/RID/'solution.rec').unlink()
        (self.root/'data'/RID/'acceptance.json').unlink()
        self.run_build()
        self.assertEqual(self.read(f'data/{RID}/record.json')['status'],'open')
        self.assertEqual(self.read('leaderboard/credits.json')['credits'],[])
        self.assertFalse((self.root/'data'/RID/'solution.html').exists())

    def test_acceptance_drives_all_exports_and_removal_clears_them(self):
        self.receipt_fixture()
        self.run_build()
        record=self.read(f'data/{RID}/record.json')
        self.assertEqual((record['status'],record['formalStatus']),('solved','proved'))
        self.assertEqual(record['render']['divisorTerms'],[[.25,[0]*6]])
        self.assertEqual(record['pullRequest']['number'],123)
        self.assertEqual(record['credit']['githubLogin'],'new-contributor')
        self.assertEqual(self.read('leaderboard/credits.json')['credits'][0]['githubLogin'],'new-contributor')
        path=self.root/'data'/RID/'solution.rec'; original=path.read_text()
        path.unlink()
        self.run_build(success=False,check=True)
        self.run_build()
        record=self.read(f'data/{RID}/record.json')
        self.assertEqual(record['status'],'open')
        self.assertNotIn('D',record)
        self.assertNotIn('divisorTerms',record['render'])
        self.assertEqual(self.read('leaderboard/credits.json')['credits'],[])
        for name in ('solution.json','solution.html'):
            self.assertFalse((path.parent/name).exists())
        path.write_text(original)
        self.run_build()
        self.run_build(check=True)

    def test_changed_binding_is_rejected_without_publishing_partial_output(self):
        self.receipt_fixture(); self.run_build()
        protected=self.root/'data'/RID
        mutations={'Solution.lean':'-- altered proof', 'solution.md':'Altered explanation',
                   'witness.json':'{}', 'instance.rec':(protected/'instance.rec').read_text().replace('q: 1','q: 2')}
        before={p:p.read_bytes() for p in self.root.rglob('*') if p.suffix in ('.json','.html') and p.name!='witness.json'}
        for name,content in mutations.items():
            with self.subTest(file=name):
                path=protected/name; original=path.read_bytes(); path.write_text(content)
                self.assertIn('has changed',self.run_build(success=False).stderr)
                path.write_bytes(original)
                self.assertEqual(before,{p:p.read_bytes() for p in before})

    def test_invalid_receipt_and_claimed_identity_cannot_publish(self):
        original=self.receipt_fixture()
        for key,value in [('formalAcceptance',False),('githubLogin','another-user')]:
            receipt=copy.deepcopy(original);receipt[key]=value
            self.write(f'data/{RID}/acceptance.json',json.dumps(receipt))
            self.run_build(success=False)
        self.write(f'data/{RID}/acceptance.json',json.dumps(original))
        path=self.root/'data'/RID/'solution.rec'; solution=yaml.safe_load(path.read_text())
        solution['solver']['githubLogin']='another-user';path.write_text(yaml.safe_dump(solution))
        self.assertIn('differs from the accepted',self.run_build(success=False).stderr)

    def test_instance_formal_flag_cannot_bypass_acceptance(self):
        path=self.root/'data'/RID/'instance.rec'
        path.write_text(path.read_text().replace('formalStatus: unproved','formalStatus: proved'))
        self.assertIn('no formal acceptance',self.run_build(success=False).stderr)

    def test_prose_math_escaping_and_ui_updates(self):
        before=self.read('data/revision.json')
        self.write(f'data/{RID}/why.md',r'A **reason** with \(X_0\) and <script>alert(1)</script>.'+'\n\n'+r'\[D^2 \mid F\]')
        self.run_build()
        rendered=(self.root/f'data/{RID}/why.html').read_text()
        self.assertIn('<strong>reason</strong>',rendered)
        self.assertIn('data-math>X_0</span>',rendered)
        self.assertIn(r'data-display>D^2 \mid F</div>',rendered)
        self.assertNotIn('<script>',rendered)
        self.assertNotEqual(before,self.read('data/revision.json'))
        before=self.read('data/revision.json')
        self.write('assets/renderer.js','// Changed renderer fixture');self.run_build()
        self.assertNotEqual(before,self.read('data/revision.json'))

    def test_math_heading_links_remain_stable(self):
        heading=r'## Solving \(E_1\) and \(E_2\)'+'\n'
        for preceding in ('',r'An earlier formula \(F^2\).'+'\n\n'):
            self.write('docs/overview.md',preceding+heading);self.run_build()
            rendered=(self.root/'docs/overview.html').read_text()
            self.assertIn('id="solving-e_1-and-e_2"',rendered)
            self.assertNotIn('hodgemathtoken',rendered.lower())

if __name__=='__main__': unittest.main()
