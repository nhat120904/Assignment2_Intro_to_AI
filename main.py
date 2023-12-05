import sys, re, regex
from sympy import symbols, Equivalent, Or, Implies, Not, And, to_cnf, parse_expr
from sympy.logic.boolalg import truth_table
from sympy.logic.inference import entails
from sympy.abc import A, B, C
from collections import deque
from itertools import product

class Clause:
    def __init__(self, content, is_true=False, premise=None, conclusion=None):
        self.content = content
        self.premise = premise
        self.conclusion = conclusion
        self.is_true = is_true
    
def tokenize(input_str):
    clauses = []
    start = 0
    end = 0

# The line `while (end := input_str.find(';', start)) != -1:` is using the walrus operator `:=` to
# assign the result of `input_str.find(';', start)` to the variable `end` while also checking if the
# result is not equal to -1.
    while (end := input_str.find(';', start)) != -1:
        clause_str = input_str[start:end].strip()
        clauses.append(Clause(clause_str, False))  # Initialize truth value to False
        start = end + 1

    # Add the last clause
    last_clause = input_str[start:].strip()
    clauses.append(Clause(last_clause, False))  # Initialize truth value to False

    return clauses

def generate_models(symbols):
    return [dict(zip(symbols, model)) for model in product([False, True], repeat=len(symbols))]

def check_entailment(kb, query, models):
    count = 0
    for model in models:
        kb_val = all(clause.content.subs(model) for clause in kb)
        query_val = query.subs(model)
        if kb_val and not query_val:
            return 0
        elif kb_val and query_val:
            count += 1
    return count

def add_brackets(expression):
    # Use a regular expression to capture both sides of "=>" or "<=>"
    result = re.sub(r'([^=<>]+)\s*(=>|<=>)\s*([^=<>]+|$)', r'(\1) \2 (\3)', expression)
    return result

def remove_redundant_bracket(s):
    p = 0
    while s != p:
        p = s
        s = regex.sub("(\(|^)\K(\((((?2)|[^()])*)\))(?=\)|$)", r"\3", s)
    return s

def parse_equivalent(expression):
    # Define a regular expression pattern for finding <=> and its operands
    pattern = re.compile(r'([^<=>\s]+) <=> ([^<=>\s]+)')

    # Replace <=> with Equivalent recursively
    while match := pattern.search(expression):
        left_operand, right_operand = match.groups()
        transformed_expression = f'Equivalent({left_operand}, {right_operand})'
        expression = expression.replace(match.group(), transformed_expression, 1)

    return expression

def forward_chaining(kb, query, symbols):
    count = {}
    entailed_symbol = []
    # count the symbols in premise of each clause
    for clause in kb:
        if clause.premise is not None:
            count[clause] = len(clause.premise.args)
            if count[clause] == 0:
                count[clause] = 1
        else:
            count[clause] = 1
    inferred = {str(symbol): False for symbol in symbols}
    agenda = [clause.content for clause in kb if len(clause.content.args) == 0]
    while agenda:
        #Pop first element in agenda
        p = agenda.pop(0)
        if str(p) not in entailed_symbol:
            entailed_symbol.append(str(p))
        if str(p) == str(query):
            #Found query in KB
            return True, entailed_symbol
        if not inferred[str(p)]:
            inferred[str(p)] = True
            for clause in kb:
                #Check if p is in premise of clause
                if str(p) in str(clause.premise):
                    count[clause] -= 1
                    if count[clause] == 0:
                        #Add conclusion to agenda
                        agenda.append(clause.conclusion)
    return False, entailed_symbol

def backward_chaining(kb, query, symbols):
    path = []

    def backward_chain(q, visited):
        nonlocal path
        if any((q == clause.conclusion and clause.premise is None) for clause in kb):
            if q not in path:
                path.append(q)
            return True
        elif not any((q == clause.conclusion) for clause in kb):
            return False
        
        for clause in kb:
            is_entailed = False
            if q == clause.conclusion:
                is_entailed = True
                if len(clause.premise.args) == 0:
                    count = list(clause.premise.args)
                    count.append(clause.premise)
                else:
                    count = list(clause.premise.args)
                for premise in count:
                    if premise == q or premise in visited:
                        is_entailed = False
                        break
                    is_entailed = is_entailed and backward_chain(premise, visited + [q])
                if is_entailed:
                    if q not in path:
                        path.append(q)
                    return True
                    
            if is_entailed:
                if q not in path:
                    path.append(q)
                return True
        if len(path) > 0:
            path.pop()
        return False
    
    result = backward_chain(query, [])
    return result, path


def main():
    if len(sys.argv) != 3:
        print("Usage: python script.py search method filename")
        sys.exit(1)

    method, filename = map(str, sys.argv[1:])
    try:
        with open(filename, 'r') as file:
            input_lines = file.readlines()
    except FileNotFoundError:
        print("Failed to open file")
        sys.exit(1)

    kb_content = ""
    query = ""
    is_kb_section = False

    for line in input_lines:
        if "TELL" in line:
            is_kb_section = True
        elif "ASK" in line:
            is_kb_section = False
        else:
            if is_kb_section:
                kb_content += line[:-1]
                kb_content = kb_content[:-1]
            else:
                query = line

    kb = tokenize(kb_content)
    #Preprocess the input Knowledge Base
    for i, clause in enumerate(kb):
        clause.content = parse_equivalent(clause.content)
        clause.content = clause.content.replace("<=>", "Equivalent(").replace("=>", ">>").replace(";", "&").replace("||", "|")
        clause.content = remove_redundant_bracket(clause.content)
        clause.content = clause.content.replace(">>", "=>")
        clause.content = add_brackets(clause.content)
        clause.content = clause.content.replace("=>", ">>")
        clause.content = parse_expr(clause.content, local_dict={})
        if len(clause.content.args) == 0:
            clause.premise = None
            clause.conclusion = clause.content
        else:
            try:
                clause.premise, clause.conclusion = clause.content.args 
            except:
                clause.premise = None
                clause.conclusion = clause.content
        kb[i] = clause

    # Parse the query and turn it to CNF
    query = add_brackets(query)
    query = query.replace("=>", ">>").replace(";", "&").replace("||", "|")
    query = parse_expr(query, local_dict={})
    query = to_cnf(query)

    # Generate models for truth table
    symbols = list(set(str(symbol) for clause in kb for symbol in clause.content.free_symbols) | set(str(symbol) for symbol in query.free_symbols))
    models = generate_models(symbols)
    
    # Run the search method
    if method.lower() == "tt":
        result = check_entailment(kb, query, models)
        if result == 0:
            print("NO")
        else:
            print("YES:", result)
    elif method.lower() == "fc":
        result = forward_chaining(kb, query, symbols)
        if result[0]:
            path = ""
            for i in range(len(result[1])):
                path += result[1][i] + ", "
            print("YES: " + path[:-2])
        else:
            print("NO")
    elif method.lower() == "bc":
        result = backward_chaining(kb, query, symbols)
        if result[0]:
            path = ""
            for i in range(len(result[1])):
                path += str(result[1][i]) + ", "
            print("YES: " + path[:-2])
        else:
            print("NO")
    else:
        print("Invalid search method")
        sys.exit(1)
        
if __name__ == "__main__":
    main()
