import unittest
import read, copy
from logical_classes import *
from student_code import KnowledgeBase
from util import * 

class KBTest(unittest.TestCase):

    # def setUp(self):
    #     # Assert starter facts
    #     file = 'statements_kb2.txt'
    #     self.data = read.read_tokenize(file)
    #     data = read.read_tokenize(file)
    #     self.KB = KnowledgeBase([], [])
    #     for item in data:
    #         if isinstance(item, Fact) or isinstance(item, Rule):
    #             self.KB.kb_assert(item)
        
    # def test1(self):
    #     # Did the student code contain syntax errors, AttributeError, etc.
    #     ask1 = read.parse_input("fact: (inst cube1 ?X)")
    #     print(' Asking if', ask1)
    #     answer = self.KB.kb_ask(ask1)
    #     print(str(answer[0]))
    #     print(str(answer[1]))
    #     #self.assertEqual(str(answer[0]), "?X : cube")

    # def test2(self):
    #     # Did the student code contain syntax errors, AttributeError, etc.
    #     ask1 = read.parse_input("fact: (coveredByed ?X)")
    #     print(' Asking if', ask1)
    #     answer = self.KB.kb_ask(ask1)
    #     print(str(answer[0]))
    
    # def test3(self):
    #     r1 = read.parse_input("fact: (inst simon red)")
    #     print(' Retracting', r1)
    #     self.KB.kb_retract(r1)
    #     ask1 = read.parse_input("fact: (coveredByed ?X)")
    #     print(' Asking if', ask1)
    #     answer = self.KB.kb_ask(ask1)
    #     print(str(answer[0]))
    #     #self.assertEqual(str(answer[0]), "?X : cube")

    def setUp(self):
        # Assert starter facts
        file = 'statements.txt'
        self.data = read.read_tokenize(file)
        data = read.read_tokenize(file)
        self.KB = KnowledgeBase([], [])
        for item in data:
            if isinstance(item, Fact) or isinstance(item, Rule):
                self.KB.kb_assert(item)

    def test(self):
        # Can fc_infer actually infer
        ask1 = read.parse_input("fact: (grandmotherof ada ?X)")
        print(' Asking if', ask1)
        answer = self.KB.kb_ask(ask1)
        self.assertEqual(str(answer[0]), "?X : chen")      
        
    # def test1(self):
    #     # Did the student code contain syntax errors, AttributeError, etc.
    #     ask1 = read.parse_input("fact: (motherof ada ?X)")
    #     print(' Asking if', ask1)
    #     answer = self.KB.kb_ask(ask1)
    #     self.assertEqual(str(answer[0]), "?X : bing")

    # def test2(self):
    #     # Can fc_infer actually infer
    #     ask1 = read.parse_input("fact: (grandmotherof ada ?X)")
    #     print(' Asking if', ask1)
    #     answer = self.KB.kb_ask(ask1)
    #     self.assertEqual(str(answer[0]), "?X : felix")
    #     self.assertEqual(str(answer[1]), "?X : chen")

    # def test3(self):
    #     # Does retract actually retract things
    #     for fact in self.KB.facts: 
    #         print(fact.__str__())
    #     r1 = read.parse_input("fact: (motherof ada bing)")
    #     print(' Retracting', r1)
    #     self.KB.kb_retract(r1)
    #     ask1 = read.parse_input("fact: (grandmotherof ada ?X)")
    #     print(' Asking if', ask1)
    #     answer = self.KB.kb_ask(ask1)
    #     self.assertEqual(len(answer), 1)
    #     self.assertEqual(str(answer[0]), "?X : felix")

    # def test4(self):
    #     # makes sure retract does not retract supported fact
    #     ask1 = read.parse_input("fact: (grandmotherof ada ?X)")
    #     print(' Asking if', ask1)
    #     answer = self.KB.kb_ask(ask1)
    #     self.assertEqual(str(answer[0]), "?X : felix")
    #     self.assertEqual(str(answer[1]), "?X : chen")

    #     r1 = read.parse_input("fact: (grandmotherof ada chen)")
    #     print(' Retracting', r1)
    #     self.KB.kb_retract(r1)

    #     print(' Asking if', ask1)
    #     answer = self.KB.kb_ask(ask1)
    #     self.assertEqual(str(answer[0]), "?X : felix")
    #     self.assertEqual(str(answer[1]), "?X : chen")
        
    # def test5(self):
    #     # makes sure retract does not deal with rules
    #     ask1 = read.parse_input("fact: (parentof ada ?X)")
    #     print(' Asking if', ask1)
    #     answer = self.KB.kb_ask(ask1)
    #     self.assertEqual(str(answer[0]), "?X : bing")
    #     r1 = read.parse_input("rule: ((motherof ?x ?y)) -> (parentof ?x ?y)")
    #     print(' Retracting', r1)
    #     self.KB.kb_retract(r1)
    #     print(' Asking if', ask1)
    #     answer = self.KB.kb_ask(ask1)
    #     self.assertEqual(str(answer[0]), "?X : bing")


def pprint_justification(answer):
    """Pretty prints (hence pprint) justifications for the answer.
    """
    if not answer: print('Answer is False, no justification')
    else:
        print('\nJustification:')
        for i in range(0,len(answer.list_of_bindings)):
            # print bindings
            print(answer.list_of_bindings[i][0])
            # print justifications
            for fact_rule in answer.list_of_bindings[i][1]:
                pprint_support(fact_rule,0)
        print

def pprint_support(fact_rule, indent):
    """Recursive pretty printer helper to nicely indent
    """
    if fact_rule:
        print(' '*indent, "Support for")

        if isinstance(fact_rule, Fact):
            print(fact_rule.statement)
        else:
            print(fact_rule.lhs, "->", fact_rule.rhs)

        if fact_rule.supported_by:
            for pair in fact_rule.supported_by:
                print(' '*(indent+1), "support option")
                for next in pair:
                    pprint_support(next, indent+2)



if __name__ == '__main__':
    unittest.main()
