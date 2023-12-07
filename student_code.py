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
            fact_rule (Fact or Rule) - Fact or Rule to be added
        Returns:
            None
        """
        printv("Adding {!r}", 1, verbose, [fact_rule])
        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:
                self.facts.append(fact_rule)
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.facts.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.facts[ind].supported_by.append(f)
                else:
                    ind = self.facts.index(fact_rule)
                    self.facts[ind].asserted = True
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

    def kb_retract(self, fact_rule):
        """Retract a fact or a rule from the KB

        Args:
            fact_rule (Fact or Rule) - Fact or Rule to be retracted

        Returns:
            None
        """
        printv("Retracting {!r}", 0, verbose, [fact_rule])
       if factq(fact_rule):
            for fact in self.facts:
                if fact_rule == fact:
                    fact_rule = fact
                    
        else:
            for rule in self.rules:
                if fact_rule == rule:
                    fact_rule = rule
                    
        if fact_rule.asserted and len(fact_rule.supported_by) != 0:
            fact_rule.asserted = False
            return
        
        for supported_fact in fact_rule.supports_facts:
            for support in supported_fact.supported_by:
                if fact_rule in support:
                    supported_fact.supported_by.remove(support)
            
            if len(supported_fact.supported_by) == 0:
                self.kb_retract(supported_fact)
                
        for supported_rule in fact_rule.supports_rules:
            for support in supported_rule.supported_by:
                if fact_rule in support:
                    supported_rule.supported_by.remove(support)
                    
            if len(supported_rule.supported_by) == 0:
                self.kb_retract(supported_rule)
                
        if len(fact_rule.supported_by) == 0:
            if factq(fact_rule):
                self.facts.remove(fact_rule)
            else:
                self.rules.remove(fact_rule)
                
        return None
    
    
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
        
        bindings = match(rule.lhs[0], fact.statement)

        if bindings:
            if len(rule.lhs) == 1:
                new_statement = instantiate(rule.rhs, bindings)
                ie_fact = Fact(new_statement, supported_by=[[rule, fact]])

                kb.kb_assert(ie_fact)
                fact.supports_facts.append(ie_fact)
                rule.supports_facts.append(ie_fact)
            else:
                new_left = []
                new_rule = []
                for rule_statement in rule.lhs[1:]:
                    new_left.append(instantiate(rule_statement, bindings))
                new_rule.append(new_left)
                
                right_new_statement = instantiate(rule.rhs, bindings)
                new_rule.append(right_new_statement)

                ie_rule = Rule(new_rule, supported_by=[[rule, fact]])

                kb.kb_assert(ie_rule)
                fact.supports_rules.append(ie_rule)
                rule.supports_rules.append(ie_rule)
        else:
            return None
        
        return None
