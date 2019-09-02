import tlcutil
import unittest
import tempfile

""" Simple tests of TLA+ expression evaluation using TLC. """

class TestTLCEval(unittest.TestCase):

	def eval_test(self, tla_expr, expected):
		tmpdir = tempfile.mkdtemp()
		tlcutil.prepare_tla_eval(tmpdir, tla_expr)
		ret = tlcutil.tlc_eval(tmpdir, tla_expr)
		self.assertEqual(ret["result"], expected)

	def test_basic_eval(self):
		self.eval_test("2+2", "4")
		self.eval_test("{x*2 : x \\in {1,2,3}}", "{2, 4, 6}")
		self.eval_test("CHOOSE x \\in {1,2,3} : x>2", "3")
		self.eval_test("(5<6) /\ (6>7)", "FALSE")

if __name__ == '__main__':
    unittest.main()