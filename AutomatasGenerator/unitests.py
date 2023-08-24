import unittest
import fsm
from pysmt.shortcuts import Symbol, And, Or, Not, Iff, Solver, get_model, is_sat, simplify, is_valid, GE, LE, Int, Equals

from pysmt.fnode import FNode
from collections import defaultdict, deque
from pysmt.typing import BOOL, INT

class MyFunctionTest(unittest.TestCase):
    def test_fsm_determinisation_1(self):
        non_deterministic_fsm = fsm.fromDot("./first_snippets/data/fsm10.dot")
        expected_fsm = fsm.fromDot("./first_snippets/data/fsm10_expected.dot")
        symbol_a = Symbol("a", BOOL)
        first_test = [[symbol_a]]
        mined_automata = fsm.precise_oracle_mining(non_deterministic_fsm, first_test, expected_fsm)
        new_fsm = mined_automata[1]
        self.assertTrue(fsm.compare_automatas(new_fsm, expected_fsm))

    def test_fsm_determinisation_2(self):
        non_deterministic_fsm = fsm.fromDot("./first_snippets/data/fsm4.dot")
        expected_fsm = fsm.fromDot("./first_snippets/data/fsm4_expected.dot")
        symbol_a = Symbol("a", BOOL)
        symbol_b = Symbol("b", BOOL)
        first_test = [[And(symbol_b, Not(symbol_a)), And(Not(symbol_b), symbol_a),And(Not(symbol_b), symbol_a)]]
        mined_automata = fsm.precise_oracle_mining(non_deterministic_fsm, first_test, expected_fsm)
        new_fsm = mined_automata[1]
        self.assertTrue(fsm.compare_automatas(new_fsm, expected_fsm))

    def test_fsm_deterministic_execution(self):
        M = fsm.fromDot("./first_snippets/data/fsm5.dot")

        result = M.deterministic_executions([Symbol('a'),Symbol('b')])

        a = Symbol("a", BOOL)
        b = Symbol("b", BOOL)
        t_0 = Symbol("t_0", BOOL)
        t_1 = Symbol("t_1", BOOL)
        t_2 = Symbol("t_2", BOOL)
        t_3 = Symbol("t_3", BOOL)

        my_set = {((a, '1', t_0), (b, '2', t_1)),
                ((a, '1', t_0), (b, '1', t_0)),
                ((a, '1', t_0), (b, '4', t_2)),
                ((a, '2', t_1), (b, '3', t_3))}
        self.assertTrue(result== my_set)
        
    def test_fsm_transitions_deletion(self):
        P = fsm.fromDot("./first_snippets/data/fsm5.dot")
        phi = And(Symbol('t_1'), Not(Symbol('t_2')), Not(Symbol('t_3')), Symbol('t_0'))

        M = fsm.create_automata_from_phi(P,phi)
        self.assertTrue(len(M.getTransitions())==2)

    def test_fsm_overlapping_transitions(self):
        non_deterministic_fsm = fsm.fromDot("./first_snippets/data/fsm12.dot")
        fsm.transform_overlapping_transitions(non_deterministic_fsm)
        transitions = non_deterministic_fsm.getTransitions()
        self.assertTrue(len(transitions)==5)
    
    def test_fsm_oracle_on_complex_transitions(self):
            non_deterministic_fsm = fsm.fromDot("./first_snippets/data/fsm11.dot")
            fsm_expected = fsm.fromDot("./first_snippets/data/fsm11_expected.dot")
            
            fsm.transform_overlapping_transitions(non_deterministic_fsm)

            symbol_b = Symbol("b", BOOL)
            symbol_c = Symbol("c", INT)
            x = GE(symbol_c, Int(6))
            y =LE(symbol_c, Int(6))
            a = And(x,y,symbol_b)
            # If you want to create a list of formulas
            input = [[a, symbol_b]]
            mined = fsm.precise_oracle_mining(non_deterministic_fsm, input, fsm_expected)
            comparaison = fsm.compare_automatas(fsm_expected, mined[1])
            self.assertTrue(comparaison[0])

if __name__ == '__main__':
    unittest.main()
