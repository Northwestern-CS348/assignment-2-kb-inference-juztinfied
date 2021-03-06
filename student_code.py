import read, copy
from util import *
from logical_classes import *

verbose = 0

class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument

        Args:
            fact (Fact): Fact we're searching for

        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument

        Args:
            rule (Rule): Rule we're searching for

        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB
        Args:
            fact_rule (Fact|Rule) - the fact or rule to be added
        Returns:
            None
        """
        printv("Adding {!r}", 1, verbose, [fact_rule])
        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts: # if the new statement (fact or rule) is not in facts
                self.facts.append(fact_rule) # add it to the kb
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self) # infer new things from the new fact
            else:
                if fact_rule.supported_by: # if the new statement is already in the kb and is supported_by stuff
                    ind = self.facts.index(fact_rule) # find the index of that fact that already is inside the kb
                    for f in fact_rule.supported_by: # for every fact that supports this fact_rule
                        self.facts[ind].supported_by.append(f)
                else:
                    ind = self.facts.index(fact_rule) # if the new fact-rule is already in the kb but is not supported by anything
                    self.facts[ind].asserted = True # consider it as asserted and so cannot be removed already
        elif isinstance(fact_rule, Rule):
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)
                else:
                    ind = self.rules.index(fact_rule)
                    self.rules[ind].asserted = True

    def kb_assert(self, fact_rule):
        """Assert a fact or rule into the KB

        Args:
            fact_rule (Fact or Rule): Fact or Rule we're asserting
        """
        printv("Asserting {!r}", 0, verbose, [fact_rule])
        self.kb_add(fact_rule)

    def kb_ask(self, fact):
        """Ask if a fact is in the KB

        Args:
            fact (Fact) - Statement to be asked (will be converted into a Fact)

        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """
        print("Asking {!r}".format(fact))
        if factq(fact):
            f = Fact(fact.statement)
            bindings_lst = ListOfBindings()
            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else []

        else:
            print("Invalid ask:", fact.statement)
            return []

    def kb_retract(self, fact_or_rule):
        printv("Retracting {!r}", 0, verbose, [fact_or_rule])
        ####################################################
        # Student code goes here
        
        if (isinstance(fact_or_rule, Rule)):
            return 
        
        elif (isinstance(fact_or_rule, Fact)):
            if fact_or_rule not in self.facts: # if the new statement (fact or rule) is not in facts
                print('the fact is not in the kb!')
                return 

            else:
                to_remove = self.facts[self.facts.index(fact_or_rule)]

                supports = to_remove.supported_by

                if supports:
                    print('the fact is supported!')
                    return 

                child_facts = to_remove.supports_facts
                child_rules = to_remove.supports_rules

                # print('here are the child facts')
                # for cf in child_facts:
                #     cf.__str__()

                # print('here are the child rules')
                # for r in child_rules:
                #     r.__str__()

                for f in child_facts: # f is one of the child fact(s) of the fact to be removed 
                    supporting_pairs = self.facts[self.facts.index(f)].supported_by # find 
                    for pair in supporting_pairs:
                        if fact_or_rule in pair:
                            supporting_pairs.remove(pair)
                    if len(supporting_pairs) == 0 and not f.asserted: # if there are no more supporting pairs to the child fact f 
                        self.kb_retract(f)

                for r in child_rules:
                    supporting_pairs = self.rules[self.rules.index(r)].supported_by
                    for pair in supporting_pairs:
                        if fact_or_rule in pair:
                            supporting_pairs.remove(pair)
                    if not supporting_pairs and not r.asserted:
                        self.rules.remove(r)

                self.facts.remove(fact_or_rule)

class InferenceEngine(object):
    def fc_infer(self, fact, rule, kb):
        """Forward-chaining to infer new facts and rules

        Args:
            fact (Fact) - A fact from the KnowledgeBase
            rule (Rule) - A rule from the KnowledgeBase
            kb (KnowledgeBase) - A KnowledgeBase

        Returns:
            Nothing            
        """
        printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
            [fact.statement, rule.lhs, rule.rhs])

        # check firs statement of LHS against the fact and see if there can be any bindings produced
        bindings = match(rule.lhs[0], fact.statement) # bindings is of type == Bindings 
        new = None

        # other checks 
        f_pred = fact.statement.predicate
        f_terms = fact.statement.terms
        f_constant = True 
        for term in f_terms:
            if isinstance(term, Variable):
                f_constant = False 

        r_pred = rule.lhs[0].predicate
        r_terms = rule.lhs[0].terms
        r_constant = True 
        for term in r_terms:
            if isinstance(term, Variable):
                r_constant = False


        # check if there are bindings 
        if bindings:
            new_lhs = list()
        
            for i in range(len(rule.lhs) - 1):
                new_lhs.append(instantiate(rule.lhs[i+1], bindings))
                
            new_rhs = instantiate(rule.rhs, bindings)

            if len(new_lhs):
                # now to make the new rule after adding a new fact 
                new = Rule([new_lhs, new_rhs],  supported_by=[[fact, rule]])

            else:
                new = Fact(new_rhs, [[fact, rule]])

        elif (f_pred == r_pred and r_terms == f_terms and f_constant == True and r_constant == True): # it could be that both fact and first lhs of rule only have constants and are exactly the same and so we are creating a new fact instead 
            lhs_count = len(rule.lhs)
            if lhs_count == 1: # if so, create a new fact 
                new = Fact(rule.rhs, [fact, rule])

            elif lhs_count > 1 : #if so, create new rule 
                new = Rule([rule.lhs[:1], rule.rhs], [fact, rule])            

        if (new and isinstance(new, Fact)): 
            kb.kb_assert(new)
            print('new fact is ')
            print(new.__str__())
            fact.supports_facts.append(new)
            rule.supports_facts.append(new)
        
        elif (new and isinstance(new, Rule)):
            kb.kb_assert(new)
            print('new rule is ')
            print(new.__str__())
            fact.supports_rules.append(new)
            rule.supports_rules.append(new)

