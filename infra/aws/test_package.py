"""The release boundary must exclude private/server material and symlinks."""
import contextlib
import importlib.util
import io
import tempfile
import unittest
from pathlib import Path

spec = importlib.util.spec_from_file_location('release_package', Path(__file__).with_name('package.py'))
release = importlib.util.module_from_spec(spec)
spec.loader.exec_module(release)


class PublicPackageTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.site = self.root / 'site'
        self.output = self.root / 'release'
        for directory in ['assets', 'data/example', 'leaderboard', 'discussions', 'docs/technical']:
            (self.site / directory).mkdir(parents=True)
        (self.site / 'index.html').write_text('<h1>Public site</h1>')

    def build(self):
        with contextlib.redirect_stdout(io.StringIO()):
            release.package(self.site, self.site, self.output, static_only=True)

    def test_public_release_excludes_private_and_unlisted_material(self):
        for name in ['.git/config', '.env', 'server/github-app.json', 'private-services/app.json',
                     'node_modules/dependency.js', 'data/.private/token.json', 'assets/unexpected.exe']:
            target = self.site / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text('PRIVATE-TEST-CONTENT')
        (self.site / 'data/example/instance.rec').write_text('F = exact target')
        (self.site / 'assets/app.js').write_text('/* public code */')
        self.build()
        files = {str(p.relative_to(self.output / 'public')) for p in (self.output / 'public').rglob('*') if p.is_file()}
        self.assertEqual(files, {'index.html', 'assets/app.js', 'data/example/instance.rec'})
        self.assertFalse((self.output / 'lambda.zip').exists())

    def test_symlink_cannot_escape_the_public_boundary(self):
        private = self.root / 'private.json'
        private.write_text('PRIVATE-TEST-CONTENT')
        (self.site / 'data/example/leak.json').symlink_to(private)
        with self.assertRaisesRegex(ValueError, 'Public symlink refused'):
            self.build()


if __name__ == '__main__':
    unittest.main()
