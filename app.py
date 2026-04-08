from flask import Flask, request, jsonify, render_template
import re
import os
from collections import defaultdict

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
app = Flask(__name__, template_folder=os.path.join(BASE_DIR, 'templates'))

# ─────────────────────────────────────────────
# UTILITY
# ─────────────────────────────────────────────

def parse_grammar(grammar_text):
    productions = defaultdict(list)
    start = None
    for line in grammar_text.strip().splitlines():
        line = line.strip()
        if not line or line.startswith('#'):
            continue
        if '->' not in line:
            continue
        lhs, rhs = line.split('->', 1)
        lhs = lhs.strip()
        if start is None:
            start = lhs
        for alt in rhs.split('|'):
            syms = alt.strip().split()
            if syms:
                productions[lhs].append(syms)
    return productions, start


def grammar_to_text(productions, order=None):
    lines = []
    keys = order if order else list(productions.keys())
    for nt in keys:
        if nt in productions:
            alts = [' '.join(alt) for alt in productions[nt]]
            lines.append(f"{nt} -> {' | '.join(alts)}")
    return '\n'.join(lines)


# ─────────────────────────────────────────────
# LEFT RECURSION ELIMINATION
# ─────────────────────────────────────────────

def eliminate_left_recursion(productions_input, start):
    steps = []
    nts = list(productions_input.keys())
    prods = {nt: [list(alt) for alt in alts] for nt, alts in productions_input.items()}

    steps.append({
        "phase": "start",
        "title": "Original Grammar",
        "description": "Starting grammar before any left recursion elimination.",
        "grammar": grammar_to_text(prods, nts)
    })

    # Check if any left recursion exists at all
    def has_any_lr():
        for nt, alts in prods.items():
            for alt in alts:
                if alt and alt[0] == nt:
                    return True
        for i, A in enumerate(nts):
            for alt in prods.get(A, []):
                if alt and alt[0] in nts[:i]:
                    return True
        return False

    if not has_any_lr():
        steps.append({
            "phase": "no_change",
            "title": "No Left Recursion Detected",
            "description": "This grammar has no immediate or indirect left recursion. No transformation needed.",
            "grammar": grammar_to_text(prods, nts)
        })
        return prods, nts, steps

    new_nts = list(nts)

    for i, Ai in enumerate(nts):
        if Ai not in prods:
            continue

        # Substitute indirect left recursion from earlier non-terminals
        for j in range(i):
            Aj = nts[j]
            if Aj not in prods:
                continue
            new_alts = []
            substituted = False
            for alt in prods[Ai]:
                if alt and alt[0] == Aj:
                    substituted = True
                    for aj_alt in prods[Aj]:
                        new_alts.append(aj_alt + alt[1:])
                else:
                    new_alts.append(alt)
            if substituted:
                before_text = grammar_to_text({Ai: prods[Ai]}, [Ai])
                prods[Ai] = new_alts
                steps.append({
                    "phase": "indirect_substitution",
                    "title": f"Substitute {Aj} into {Ai}",
                    "description": (
                        f"Productions of <b>{Ai}</b> that begin with <b>{Aj}</b> "
                        f"are expanded using all alternatives of <b>{Aj}</b>."
                    ),
                    "before": before_text,
                    "substitution": grammar_to_text({Aj: prods[Aj]}, [Aj]),
                    "after": grammar_to_text({Ai: new_alts}, [Ai]),
                    "grammar": grammar_to_text(prods, new_nts)
                })

        # Eliminate immediate left recursion for Ai
        recursive = [alt for alt in prods[Ai] if alt and alt[0] == Ai]
        non_recursive = [alt for alt in prods[Ai] if not (alt and alt[0] == Ai)]

        if recursive:
            Ai_prime = Ai + "'"
            while Ai_prime in prods or Ai_prime in new_nts:
                Ai_prime += "'"

            before_text = grammar_to_text({Ai: prods[Ai]}, [Ai])
            new_nts.append(Ai_prime)

            prods[Ai] = [nr + [Ai_prime] for nr in non_recursive] if non_recursive else [[Ai_prime]]
            prods[Ai_prime] = [r[1:] + [Ai_prime] for r in recursive] + [['ε']]

            steps.append({
                "phase": "immediate_elimination",
                "title": f"Eliminate Immediate Left Recursion in {Ai}",
                "description": (
                    f"<b>{Ai}</b> has immediate left recursion. "
                    f"Introducing <b>{Ai_prime}</b> to handle the recursive tail.<br>"
                    f"Recursive alts: <code>{'  |  '.join(' '.join(r) for r in recursive)}</code><br>"
                    f"Non-recursive alts: <code>{'  |  '.join(' '.join(nr) for nr in non_recursive) if non_recursive else 'ε'}</code>"
                ),
                "before": before_text,
                "after": grammar_to_text({Ai: prods[Ai], Ai_prime: prods[Ai_prime]}, [Ai, Ai_prime]),
                "grammar": grammar_to_text(prods, new_nts)
            })

    steps.append({
        "phase": "result",
        "title": "Left Recursion Eliminated",
        "description": "All immediate and indirect left recursion has been removed.",
        "grammar": grammar_to_text(prods, new_nts)
    })

    return prods, new_nts, steps


# ─────────────────────────────────────────────
# LEFT FACTORING
# ─────────────────────────────────────────────

def left_factor(productions_input, nt_order):
    steps = []
    prods = {nt: [list(alt) for alt in alts] for nt, alts in productions_input.items()}
    new_order = list(nt_order)

    steps.append({
        "phase": "start",
        "title": "Grammar Before Left Factoring",
        "description": "Starting grammar (post left-recursion elimination if applied).",
        "grammar": grammar_to_text(prods, new_order)
    })

    any_factored = False
    changed = True
    iteration = 0

    while changed and iteration < 30:
        changed = False
        iteration += 1
        for nt in list(new_order):
            if nt not in prods:
                continue
            alts = prods[nt]
            if len(alts) < 2:
                continue

            # Group alts by first symbol
            groups = defaultdict(list)
            for alt in alts:
                if alt and alt != ['ε']:
                    groups[alt[0]].append(alt)

            factored_this = False
            for prefix_sym, group in groups.items():
                if len(group) < 2:
                    continue

                # Find longest common prefix
                lcp = list(group[0])
                for g in group[1:]:
                    new_lcp = []
                    for a, b in zip(lcp, g):
                        if a == b:
                            new_lcp.append(a)
                        else:
                            break
                    lcp = new_lcp
                    if not lcp:
                        break

                if not lcp:
                    continue

                # Build new non-terminal
                new_nt = nt + "'"
                while new_nt in prods or new_nt in new_order:
                    new_nt += "'"

                before_text = grammar_to_text({nt: alts}, [nt])

                # Suffixes for the new NT
                suffix_alts = []
                for g in group:
                    suffix = g[len(lcp):]
                    suffix_alts.append(suffix if suffix else ['ε'])

                # Remaining alts not in this group
                remaining = [alt for alt in alts if not (
                    len(alt) >= len(lcp) and alt[:len(lcp)] == lcp
                )]

                prods[nt] = remaining + [lcp + [new_nt]]
                prods[new_nt] = suffix_alts
                new_order.insert(new_order.index(nt) + 1, new_nt)

                steps.append({
                    "phase": "factoring",
                    "title": f"Factor {nt} on common prefix '{' '.join(lcp)}'",
                    "description": (
                        f"Productions of <b>{nt}</b> share prefix <code>{' '.join(lcp)}</code>.<br>"
                        f"Grouped: <code>{'  |  '.join(' '.join(g) for g in group)}</code><br>"
                        f"New non-terminal <b>{new_nt}</b> introduced for suffixes."
                    ),
                    "before": before_text,
                    "after": grammar_to_text({nt: prods[nt], new_nt: prods[new_nt]}, [nt, new_nt]),
                    "grammar": grammar_to_text(prods, new_order)
                })

                changed = True
                any_factored = True
                factored_this = True
                break

            if factored_this:
                break

    if not any_factored:
        steps.append({
            "phase": "no_change",
            "title": "No Left Factoring Needed",
            "description": "The grammar has no common prefixes among alternatives. No factoring required.",
            "grammar": grammar_to_text(prods, new_order)
        })
    else:
        steps.append({
            "phase": "result",
            "title": "Left Factoring Complete",
            "description": "All common prefixes have been factored out. Grammar is now LL(1)-ready.",
            "grammar": grammar_to_text(prods, new_order)
        })

    return prods, new_order, steps


# ─────────────────────────────────────────────
# 1. SHIFT-REDUCE PARSING
# ─────────────────────────────────────────────

def shift_reduce_parse(grammar_text, input_string):
    productions, start = parse_grammar(grammar_text)
    if not productions:
        return {"error": "Invalid grammar — no productions found."}

    rules = []
    for lhs, alts in productions.items():
        for rhs in alts:
            rules.append((lhs, rhs))

    tokens = input_string.strip().split() + ['$']
    stack = []
    idx = 0
    steps = []
    MAX_STEPS = 200
    reject_reason = None

    def try_reduce(stack):
        for lhs, rhs in rules:
            if len(stack) >= len(rhs) and stack[-len(rhs):] == list(rhs):
                return lhs, rhs
        return None, None

    while True:
        if len(steps) > MAX_STEPS:
            reject_reason = f"Exceeded maximum steps ({MAX_STEPS}). The grammar may be ambiguous or left-recursive."
            steps.append({"stack": list(stack), "input": tokens[idx:], "action": f"ERROR: {reject_reason}"})
            break

        remaining = tokens[idx:]
        lhs, rhs = try_reduce(stack)

        if lhs:
            action = f"Reduce by {lhs} → {' '.join(rhs)}"
            steps.append({"stack": list(stack), "input": list(remaining), "action": action})
            for _ in rhs:
                stack.pop()
            stack.append(lhs)
            if stack == [start] and tokens[idx:] == ['$']:
                steps.append({"stack": list(stack), "input": ['$'], "action": "ACCEPT"})
                break
        elif idx < len(tokens):
            sym = tokens[idx]
            if sym == '$' and stack == [start]:
                steps.append({"stack": list(stack), "input": ['$'], "action": "ACCEPT"})
                break
            if sym == '$':
                top = stack[-1] if stack else "empty"
                reject_reason = (
                    f"Input exhausted but stack still contains '{top}'. "
                    f"The partial input '{' '.join(tokens[:-1])}' cannot be reduced to the start symbol '{start}'. "
                    f"Possible fix: check if all tokens form a complete valid phrase."
                )
                steps.append({"stack": list(stack), "input": list(remaining), "action": f"ERROR: {reject_reason}"})
                break
            action = f"Shift '{sym}'"
            steps.append({"stack": list(stack), "input": list(remaining), "action": action})
            stack.append(sym)
            idx += 1
        else:
            top = stack[-1] if stack else "empty"
            reject_reason = (
                f"Cannot shift (no more input) and cannot reduce top of stack '{top}'. "
                f"No grammar rule matches the current stack configuration. "
                f"The token sequence does not conform to any production rule."
            )
            steps.append({"stack": list(stack), "input": [], "action": f"ERROR: {reject_reason}"})
            break

    accepted = any(s["action"] == "ACCEPT" for s in steps)
    return {"steps": steps, "accepted": accepted, "reject_reason": reject_reason if not accepted else None}


# ─────────────────────────────────────────────
# 2. RECURSIVE DESCENT PARSING
# ─────────────────────────────────────────────

def recursive_descent_parse(grammar_text, input_string):
    productions, start = parse_grammar(grammar_text)
    if not productions:
        return {"error": "Invalid grammar — no productions found."}

    tokens = input_string.strip().split()
    pos = [0]
    trace = []
    reject_reason = [None]

    def match(sym):
        if pos[0] < len(tokens) and tokens[pos[0]] == sym:
            trace.append(f"match('{sym}') at pos {pos[0]}")
            pos[0] += 1
            return True
        got = tokens[pos[0]] if pos[0] < len(tokens) else 'end-of-input'
        trace.append(f"✗ expected '{sym}', got '{got}' at pos {pos[0]}")
        return False

    def parse_nt(nt, depth=0):
        if depth > 50:
            reject_reason[0] = "Recursion depth exceeded — grammar may be infinitely recursive."
            return False
        if nt not in productions:
            return match(nt)
        indent = "  " * depth
        trace.append(f"{indent}enter {nt}")
        for alt in productions[nt]:
            saved = pos[0]
            trace.append(f"{indent}  try {nt} → {' '.join(alt)}")
            ok = True
            for sym in alt:
                if sym == 'ε' or sym == 'eps':
                    continue
                if not parse_nt(sym, depth + 1):
                    ok = False
                    break
            if ok:
                trace.append(f"{indent}  ✓ matched {nt} → {' '.join(alt)}")
                return True
            pos[0] = saved
        trace.append(f"{indent}✗ {nt} failed — all alternatives exhausted")
        return False

    success = parse_nt(start) and pos[0] == len(tokens)

    if not success and not reject_reason[0]:
        if pos[0] < len(tokens):
            consumed = ' '.join(tokens[:pos[0]])
            remaining = ' '.join(tokens[pos[0]:])
            reject_reason[0] = (
                f"Parsing stopped at token '{tokens[pos[0]]}' (position {pos[0]}). "
                f"Successfully parsed: '{consumed}'. "
                f"Unexpected tokens remaining: '{remaining}'. "
                f"No alternative in the grammar can consume these tokens."
            )
        else:
            reject_reason[0] = (
                f"All input tokens were consumed but the start symbol '{start}' "
                f"could not be fully derived. The grammar expects more tokens or "
                f"a different structure."
            )

    # Generate C program
    c_lines = ['#include <stdio.h>', '#include <string.h>', '#include <stdlib.h>', '',
               'char *input[256];', 'int pos = 0;', 'int n = 0;', '',
               'int match(const char *sym) {',
               '    if (pos < n && strcmp(input[pos], sym) == 0) { pos++; return 1; }',
               '    return 0;', '}', '']

    for nt in productions:
        safe = re.sub(r"[^a-zA-Z0-9_]", "_", nt)
        c_lines.append(f"int parse_{safe}();")
    c_lines.append('')

    for nt, alts in productions.items():
        safe = re.sub(r"[^a-zA-Z0-9_]", "_", nt)
        c_lines.append(f"int parse_{safe}() {{")
        c_lines.append(f"    int saved;")
        for alt in alts:
            c_lines.append(f"    saved = pos;")
            conditions = []
            for sym in alt:
                if sym in ('ε', 'eps'):
                    conditions.append('1')
                elif sym in productions:
                    s2 = re.sub(r"[^a-zA-Z0-9_]", "_", sym)
                    conditions.append(f"parse_{s2}()")
                else:
                    conditions.append(f'match("{sym}")')
            c_lines.append(f"    if ({' && '.join(conditions)}) return 1;")
            c_lines.append(f"    pos = saved;")
        c_lines.append(f"    return 0;")
        c_lines.append(f"}}")
        c_lines.append('')

    start_safe = re.sub(r"[^a-zA-Z0-9_]", "_", start)
    c_lines += [
        'int main() {',
        '    char buf[64];',
        '    printf("Enter tokens (end with EOF):\\n");',
        '    while (scanf("%s", buf) == 1) {',
        '        input[n] = malloc(strlen(buf)+1);',
        '        strcpy(input[n++], buf);',
        '    }',
        f'    if (parse_{start_safe}() && pos == n)',
        '        printf("Input ACCEPTED\\n");',
        '    else',
        '        printf("Input REJECTED\\n");',
        '    return 0;',
        '}'
    ]

    return {
        "accepted": success,
        "trace": trace,
        "c_program": "\n".join(c_lines),
        "reject_reason": reject_reason[0] if not success else None
    }


# ─────────────────────────────────────────────
# 3. PREDICTIVE (LL(1)) PARSING
# ─────────────────────────────────────────────

def compute_first(productions):
    first = defaultdict(set)
    non_terminals = set(productions.keys())
    changed = True
    while changed:
        changed = False
        for nt, alts in productions.items():
            for alt in alts:
                if alt == ['ε'] or alt == ['eps']:
                    if 'ε' not in first[nt]:
                        first[nt].add('ε')
                        changed = True
                else:
                    for sym in alt:
                        if sym not in non_terminals:
                            if sym not in first[nt]:
                                first[nt].add(sym)
                                changed = True
                            break
                        else:
                            before = len(first[nt])
                            first[nt] |= (first[sym] - {'ε'})
                            if len(first[nt]) != before:
                                changed = True
                            if 'ε' not in first[sym]:
                                break
                    else:
                        if 'ε' not in first[nt]:
                            first[nt].add('ε')
                            changed = True
    return first


def compute_follow(productions, start, first):
    follow = defaultdict(set)
    follow[start].add('$')
    non_terminals = set(productions.keys())
    changed = True
    while changed:
        changed = False
        for nt, alts in productions.items():
            for alt in alts:
                for i, sym in enumerate(alt):
                    if sym not in non_terminals:
                        continue
                    rest = alt[i+1:]
                    rest_first = set()
                    all_eps = True
                    for s in rest:
                        if s not in non_terminals:
                            rest_first.add(s)
                            all_eps = False
                            break
                        rest_first |= (first[s] - {'ε'})
                        if 'ε' not in first[s]:
                            all_eps = False
                            break
                    before = len(follow[sym])
                    follow[sym] |= (rest_first - {'ε'})
                    if all_eps or not rest:
                        follow[sym] |= follow[nt]
                    if len(follow[sym]) != before:
                        changed = True
    return follow


def build_parsing_table(productions, first, follow):
    table = defaultdict(dict)
    non_terminals = set(productions.keys())
    for nt, alts in productions.items():
        for alt in alts:
            alt_first = set()
            all_eps = True
            if alt == ['ε'] or alt == ['eps']:
                alt_first.add('ε')
            else:
                for sym in alt:
                    if sym not in non_terminals:
                        alt_first.add(sym)
                        all_eps = False
                        break
                    alt_first |= (first[sym] - {'ε'})
                    if 'ε' not in first[sym]:
                        all_eps = False
                        break
            for t in alt_first:
                if t != 'ε':
                    table[nt][t] = alt
            if 'ε' in alt_first or all_eps:
                for t in follow[nt]:
                    table[nt][t] = alt
    return table


def predictive_parse(grammar_text, input_string):
    productions, start = parse_grammar(grammar_text)
    if not productions:
        return {"error": "Invalid grammar — no productions found."}

    # ── Grammar transformations ──────────────────────────────────
    lr_prods, lr_order, lr_steps = eliminate_left_recursion(productions, start)
    lf_prods, lf_order, lf_steps = left_factor(lr_prods, lr_order)

    transformed_grammar_text = grammar_to_text(lf_prods, lf_order)
    final_productions, final_start = parse_grammar(transformed_grammar_text)

    # ── LL(1) on the transformed grammar ────────────────────────
    first = compute_first(final_productions)
    follow = compute_follow(final_productions, final_start, first)
    table = build_parsing_table(final_productions, first, follow)

    first_s = {k: sorted(v) for k, v in first.items()}
    follow_s = {k: sorted(v) for k, v in follow.items()}

    non_terminals = sorted(final_productions.keys())
    all_terminals = set()
    for nt in non_terminals:
        all_terminals |= set(table[nt].keys())
    all_terminals = sorted(all_terminals)

    table_display = []
    for nt in non_terminals:
        row = {"NT": nt}
        for t in all_terminals:
            if t in table[nt]:
                row[t] = f"{nt} → {' '.join(table[nt][t])}"
            else:
                row[t] = ""
        table_display.append(row)

    tokens = input_string.strip().split() + ['$']
    stack = ['$', final_start]
    idx = 0
    steps = []
    MAX_STEPS = 200
    accepted = False
    error = None
    reject_reason = None

    while stack and len(steps) < MAX_STEPS:
        top = stack[-1]
        cur = tokens[idx] if idx < len(tokens) else '$'
        step = {"stack": list(reversed(stack)), "input": tokens[idx:], "output": ""}

        if top == '$' and cur == '$':
            step["output"] = "ACCEPT"
            steps.append(step)
            accepted = True
            break
        elif top == cur:
            step["output"] = f"Match '{cur}'"
            steps.append(step)
            stack.pop()
            idx += 1
        elif top not in final_productions:
            reject_reason = (
                f"Terminal mismatch: expected '{top}' on stack but found '{cur}' in input. "
                f"The grammar requires '{top}' at this position, but the input provides '{cur}'. "
                f"Check for missing or extra tokens around position {idx}."
            )
            step["output"] = f"ERROR: {reject_reason}"
            steps.append(step)
            error = step["output"]
            break
        elif cur in table[top]:
            prod = table[top][cur]
            step["output"] = f"{top} → {' '.join(prod)}"
            steps.append(step)
            stack.pop()
            if prod != ['ε'] and prod != ['eps']:
                for sym in reversed(prod):
                    stack.append(sym)
        else:
            first_of_top = sorted(first.get(top, set()) - {'ε'})
            follow_of_top = sorted(follow.get(top, set()))
            reject_reason = (
                f"No entry in parsing table for M[{top}, '{cur}']. "
                f"Non-terminal '{top}' cannot start with '{cur}'. "
                f"FIRST({top}) = {{{', '.join(first_of_top)}}}. "
                f"FOLLOW({top}) = {{{', '.join(follow_of_top)}}}. "
                f"Token '{cur}' is not in either set, so no valid derivation exists."
            )
            step["output"] = f"ERROR: {reject_reason}"
            steps.append(step)
            error = step["output"]
            break

    return {
        "first": first_s,
        "follow": follow_s,
        "table": table_display,
        "terminals": all_terminals,
        "steps": steps,
        "accepted": accepted,
        "error": error,
        "reject_reason": reject_reason,
        # ── Transformation data for frontend visualization ────────
        "lr_steps": lr_steps,
        "lf_steps": lf_steps,
        "original_grammar": grammar_text.strip(),
        "transformed_grammar": transformed_grammar_text
    }


# ─────────────────────────────────────────────
# 4. OPERATOR PRECEDENCE PARSING
# ─────────────────────────────────────────────

def operator_precedence_parse(grammar_text, input_string):
    productions, start = parse_grammar(grammar_text)

    op_prec = {'+': 1, '-': 1, '*': 2, '/': 2, '^': 3, '(': 0, ')': 0, '$': -1}

    def get_prec(op):
        return op_prec.get(op, 1)

    def relation(a, b):
        if a == '$':
            return '<'
        if a == '(' and b == ')':
            return '='
        if a == '(':
            return '<'
        if b == ')':
            return '>'
        if b == '(':
            return '<'
        if b == '$':
            return '>'
        pa, pb = get_prec(a), get_prec(b)
        if pa < pb:
            return '<'
        return '>'

    tokens = input_string.strip().split() + ['$']
    stack = ['$']
    idx = 0
    steps = []
    accepted = False
    MAX_STEPS = 150
    reject_reason = None

    def top_operator(stk):
        for s in reversed(stk):
            if s in op_prec:
                return s
        return '$'

    while len(steps) < MAX_STEPS:
        cur = tokens[idx] if idx < len(tokens) else '$'
        top_op = top_operator(stack)

        cur_is_op = cur in op_prec
        if cur_is_op:
            rel = relation(top_op, cur)
        else:
            rel = 'shift'

        step = {
            "stack": list(stack),
            "input": tokens[idx:],
            "relation": rel,
            "action": ""
        }

        if top_op == '$' and cur == '$':
            step["action"] = "ACCEPT"
            step["relation"] = "="
            steps.append(step)
            accepted = True
            break

        if rel == 'shift' or rel == '<' or rel == '=':
            step["action"] = f"Shift '{cur}'"
            steps.append(step)
            stack.append(cur)
            idx += 1
        elif rel == '>':
            popped = []
            while stack:
                sym = stack.pop()
                popped.insert(0, sym)
                prev_op = top_operator(stack)
                if relation(prev_op, sym if sym in op_prec else popped[0]) == '<':
                    break
                if prev_op == '$':
                    break
            stack.append('E')
            step["action"] = f"Reduce '{' '.join(popped)}' → E"
            steps.append(step)
        else:
            reject_reason = (
                f"No precedence relation defined for operators ['{top_op}', '{cur}']. "
                f"The operator '{cur}' cannot follow '{top_op}' according to operator precedence rules. "
                f"Check that all operators in the input are supported: +, -, *, /, ^."
            )
            step["action"] = f"ERROR: {reject_reason}"
            steps.append(step)
            break

    if not accepted and not reject_reason:
        last_stack = steps[-1]["stack"] if steps else stack
        reject_reason = (
            f"Expression could not be fully reduced. "
            f"Remaining stack: {last_stack}. "
            f"This may indicate unmatched parentheses, a missing operand, or an incomplete expression."
        )

    return {"steps": steps, "accepted": accepted, "reject_reason": reject_reason if not accepted else None}


# ─────────────────────────────────────────────
# 5. SLR(1) PARSING
# ─────────────────────────────────────────────

def slr_parse(grammar_text, input_string):
    productions, start = parse_grammar(grammar_text)
    if not productions:
        return {"error": "Invalid grammar — no productions found."}

    aug_start = start + "'"
    aug_productions = {aug_start: [[start]]}
    for nt, alts in productions.items():
        aug_productions[nt] = alts
    all_nts = set(aug_productions.keys())

    rules = [(aug_start, [start])]
    for nt, alts in productions.items():
        for rhs in alts:
            rules.append((nt, rhs))

    def closure(items):
        result = set(items)
        changed = True
        while changed:
            changed = False
            for (ri, dot) in list(result):
                rhs = rules[ri][1]
                if dot < len(rhs):
                    sym = rhs[dot]
                    if sym in all_nts:
                        for i, (lhs, r) in enumerate(rules):
                            if lhs == sym:
                                item = (i, 0)
                                if item not in result:
                                    result.add(item)
                                    changed = True
        return frozenset(result)

    def goto(items, sym):
        moved = set()
        for (ri, dot) in items:
            rhs = rules[ri][1]
            if dot < len(rhs) and rhs[dot] == sym:
                moved.add((ri, dot + 1))
        return closure(moved) if moved else frozenset()

    start_item = closure({(0, 0)})
    states = [start_item]
    state_map = {start_item: 0}
    transitions = {}

    worklist = [start_item]
    while worklist:
        state = worklist.pop(0)
        sid = state_map[state]
        syms = set()
        for (ri, dot) in state:
            rhs = rules[ri][1]
            if dot < len(rhs):
                syms.add(rhs[dot])
        for sym in syms:
            next_state = goto(state, sym)
            if not next_state:
                continue
            if next_state not in state_map:
                state_map[next_state] = len(states)
                states.append(next_state)
                worklist.append(next_state)
            transitions[(sid, sym)] = state_map[next_state]

    first = compute_first(productions)
    follow = compute_follow(productions, start, first)
    follow[aug_start] = {'$'}

    action = defaultdict(dict)
    goto_table = defaultdict(dict)
    conflicts = []

    for state in states:
        sid = state_map[state]
        for sym in set(aug_productions.keys()) | set(productions.keys()):
            if (sid, sym) in transitions:
                ns = transitions[(sid, sym)]
                if sym in all_nts:
                    goto_table[sid][sym] = ns
                else:
                    if sym in action[sid]:
                        conflicts.append(f"Shift-shift conflict at state {sid} on '{sym}'")
                    action[sid][sym] = ('shift', ns)

        for (ri, dot) in state:
            lhs, rhs = rules[ri]
            if dot == len(rhs):
                if lhs == aug_start:
                    action[sid]['$'] = ('accept',)
                else:
                    for t in follow.get(lhs, set()):
                        if t in action[sid]:
                            existing = action[sid][t]
                            if existing[0] == 'shift':
                                conflicts.append(
                                    f"Shift-Reduce conflict at state {sid} on '{t}': "
                                    f"shift to state {existing[1]} vs reduce by rule {ri} ({lhs} → {' '.join(rhs)})"
                                )
                            elif existing[0] == 'reduce' and existing[1] != ri:
                                conflicts.append(
                                    f"Reduce-Reduce conflict at state {sid} on '{t}': "
                                    f"rule {existing[1]} vs rule {ri}"
                                )
                        else:
                            action[sid][t] = ('reduce', ri)

    if conflicts:
        return {
            "error": "Grammar is not SLR(1)",
            "reject_reason": (
                f"This grammar has {len(conflicts)} conflict(s) and is NOT SLR(1):\n" +
                "\n".join(f"  • {c}" for c in conflicts)
            ),
            "accepted": False,
            "conflicts": conflicts
        }

    all_terminals = set()
    for sid_actions in action.values():
        all_terminals |= set(sid_actions.keys())
    all_terminals = sorted(all_terminals)
    all_nts_list = sorted(all_nts - {aug_start})

    action_table_display = []
    for sid in range(len(states)):
        row = {"state": sid}
        for t in all_terminals:
            if t in action[sid]:
                a = action[sid][t]
                if a[0] == 'shift':
                    row[t] = f"s{a[1]}"
                elif a[0] == 'reduce':
                    ri = a[1]
                    row[t] = f"r{ri} ({rules[ri][0]}→{' '.join(rules[ri][1])})"
                elif a[0] == 'accept':
                    row[t] = "acc"
            else:
                row[t] = ""
        action_table_display.append(row)

    goto_table_display = []
    for sid in range(len(states)):
        row = {"state": sid}
        for nt in all_nts_list:
            row[nt] = goto_table[sid].get(nt, "")
        goto_table_display.append(row)

    state_items_display = []
    for i, state in enumerate(states):
        items_str = []
        for (ri, dot) in sorted(state):
            lhs, rhs = rules[ri]
            r = list(rhs)
            r.insert(dot, '•')
            items_str.append(f"{lhs} → {' '.join(r)}")
        state_items_display.append({"state": i, "items": sorted(items_str)})

    tokens = input_string.strip().split() + ['$']
    state_stack = [0]
    sym_stack = ['$']
    idx = 0
    steps = []
    accepted = False
    reject_reason = None
    MAX_STEPS = 200

    while len(steps) < MAX_STEPS:
        cur_state = state_stack[-1]
        cur_tok = tokens[idx] if idx < len(tokens) else '$'

        step = {
            "state_stack": list(state_stack),
            "sym_stack": list(sym_stack),
            "input": tokens[idx:],
            "action": ""
        }

        if cur_tok not in action[cur_state]:
            valid_tokens = [t for t in action[cur_state] if action[cur_state][t]]
            reject_reason = (
                f"No action defined for state {cur_state} on input token '{cur_tok}'. "
                f"In state {cur_state}, valid lookahead tokens are: {{{', '.join(sorted(valid_tokens))}}}. "
                f"Token '{cur_tok}' is unexpected here. "
                f"This indicates the token sequence violates the grammar structure at this point."
            )
            step["action"] = f"ERROR: {reject_reason}"
            steps.append(step)
            break

        act = action[cur_state][cur_tok]

        if act[0] == 'shift':
            ns = act[1]
            step["action"] = f"Shift '{cur_tok}', go to state {ns}"
            steps.append(step)
            state_stack.append(ns)
            sym_stack.append(cur_tok)
            idx += 1

        elif act[0] == 'reduce':
            ri = act[1]
            lhs, rhs = rules[ri]
            for _ in rhs:
                state_stack.pop()
                sym_stack.pop()
            top_state = state_stack[-1]
            if lhs not in goto_table[top_state]:
                reject_reason = (
                    f"GOTO table missing entry for state {top_state} on '{lhs}' after reducing by rule {ri}. "
                    f"This is a parser construction error."
                )
                step["action"] = f"ERROR: {reject_reason}"
                steps.append(step)
                break
            ns = goto_table[top_state][lhs]
            step["action"] = f"Reduce by rule {ri}: {lhs} → {' '.join(rhs)}, go to state {ns}"
            steps.append(step)
            state_stack.append(ns)
            sym_stack.append(lhs)

        elif act[0] == 'accept':
            step["action"] = "ACCEPT"
            steps.append(step)
            accepted = True
            break

    return {
        "steps": steps,
        "accepted": accepted,
        "reject_reason": reject_reason if not accepted else None,
        "action_table": action_table_display,
        "goto_table": goto_table_display,
        "terminals": all_terminals,
        "nonterminals": all_nts_list,
        "state_items": state_items_display,
        "rules": [f"{r[0]} → {' '.join(r[1])}" for r in rules]
    }


# ─────────────────────────────────────────────
# ROUTES
# ─────────────────────────────────────────────

@app.route('/')
def index():
    return render_template('index.html')


@app.route('/parse', methods=['POST'])
def parse():
    data = request.get_json()
    method = data.get('method', '')
    grammar = data.get('grammar', '')
    inp = data.get('input', '')

    if method == 'shift_reduce':
        return jsonify(shift_reduce_parse(grammar, inp))
    elif method == 'recursive_descent':
        return jsonify(recursive_descent_parse(grammar, inp))
    elif method == 'predictive':
        return jsonify(predictive_parse(grammar, inp))
    elif method == 'operator_precedence':
        return jsonify(operator_precedence_parse(grammar, inp))
    elif method == 'slr':
        return jsonify(slr_parse(grammar, inp))
    else:
        return jsonify({"error": "Unknown parsing method"})


if __name__ == '__main__':
    app.run(debug=True)