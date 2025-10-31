import streamlit as st
from collections import defaultdict
import itertools
import graphviz
import re

EPS = 'ε'

# -----------------------
# expand_plus: a+ -> a.a* , (expr)+ -> (expr).(expr)*
# -----------------------
def expand_plus(regex):
    # Remplace ( ... )+ en ( ... ).( ... )* et sym+ en sym.sym*
    pattern_group = re.compile(r'(\([^()]+\))\+')
    pattern_sym = re.compile(r'([A-Za-z0-9])\+')
    prev = None
    s = regex
    while prev != s:
        prev = s
        s = pattern_group.sub(r'\1.\1*', s)
        s = pattern_sym.sub(r'\1.\1*', s)
    return s

# -------------------------
# Helpers : regex -> postfix
# -------------------------
def insert_concat(regex):
    res = []
    prev = None
    symbols = set("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789")
    for c in regex:
        if prev is not None:
            if (prev in symbols or prev in ")*?") and (c in symbols or c == '('):
                res.append('.')
        res.append(c)
        prev = c
    return ''.join(res)

def to_postfix(regex):
    # opérateurs: * ? (unaires), . concat, | alternation
    prec = {'*':3, '?':3, '.':2, '|':1}
    output = []
    stack = []
    i = 0
    while i < len(regex):
        c = regex[i]
        if c.isalnum():
            output.append(c)
        elif c == '(':
            stack.append(c)
        elif c == ')':
            while stack and stack[-1] != '(':
                output.append(stack.pop())
            if not stack:
                raise ValueError("Parenthèse fermante sans ouvrante")
            stack.pop()
        else:
            while stack and stack[-1] != '(' and prec.get(stack[-1],0) >= prec.get(c,0):
                output.append(stack.pop())
            stack.append(c)
        i += 1
    while stack:
        op = stack.pop()
        if op in '()':
            raise ValueError("Parenthèses mal appariées")
        output.append(op)
    return ''.join(output)

# -------------------------
# Thompson construction (un seul accept final garanti)
# -------------------------
class Fragment:
    def __init__(self, start, accept):
        self.start = start
        self.accept = accept

def thompson_with_steps(postfix):
    transitions = defaultdict(list)
    counter = itertools.count()
    stack = []
    steps = []

    def snapshot(tok, new_transitions):
        copy_trans = {s: list(lst) for s, lst in transitions.items()}
        stack_repr = [f"[{frag.start}->{frag.accept}]" for frag in stack]
        steps.append({'tok': tok, 'stack': list(stack_repr), 'transitions': copy_trans, 'new': new_transitions})

    for tok in postfix:
        new_trans = []
        if tok.isalnum():
            s = next(counter); a = next(counter)
            transitions[s].append((tok, a))
            transitions.setdefault(a, [])   # assure que l'état accept existe dans le dict
            new_trans.append((s, tok, a))
            stack.append(Fragment(s, a))
        elif tok == '.':
            if len(stack) < 2:
                raise ValueError("Concat : pile trop petite")
            f2 = stack.pop(); f1 = stack.pop()
            transitions[f1.accept].append((EPS, f2.start))
            new_trans.append((f1.accept, EPS, f2.start))
            stack.append(Fragment(f1.start, f2.accept))
        elif tok == '|':
            if len(stack) < 2:
                raise ValueError("Alternation : pile trop petite")
            f2 = stack.pop(); f1 = stack.pop()
            s = next(counter); a = next(counter)
            transitions[s].append((EPS, f1.start))
            transitions[s].append((EPS, f2.start))
            transitions[f1.accept].append((EPS, a))
            transitions[f2.accept].append((EPS, a))
            transitions.setdefault(s, [])
            transitions.setdefault(a, [])
            new_trans += [(s, EPS, f1.start), (s, EPS, f2.start), (f1.accept, EPS, a), (f2.accept, EPS, a)]
            stack.append(Fragment(s, a))
        elif tok == '*':
            if len(stack) < 1:
                raise ValueError("Kleene : pile trop petite")
            f = stack.pop()
            s = next(counter); a = next(counter)
            transitions[s].append((EPS, f.start))
            transitions[s].append((EPS, a))
            transitions[f.accept].append((EPS, f.start))
            transitions[f.accept].append((EPS, a))
            transitions.setdefault(s, [])
            transitions.setdefault(a, [])
            new_trans += [(s, EPS, f.start), (s, EPS, a), (f.accept, EPS, f.start), (f.accept, EPS, a)]
            stack.append(Fragment(s, a))
        elif tok == '?':
            if len(stack) < 1:
                raise ValueError("Option : pile trop petite")
            f = stack.pop()
            s = next(counter); a = next(counter)
            transitions[s].append((EPS, f.start))
            transitions[s].append((EPS, a))
            transitions[f.accept].append((EPS, a))
            transitions.setdefault(s, [])
            transitions.setdefault(a, [])
            new_trans += [(s, EPS, f.start), (s, EPS, a), (f.accept, EPS, a)]
            stack.append(Fragment(s, a))
        else:
            raise ValueError(f"Symbole non supporté: {tok}")
        snapshot(tok, new_trans)

    if len(stack) != 1:
        raise ValueError("Expression invalide : la pile finale doit contenir exactement un fragment")

    frag = stack.pop()
    final_nfa = {'start': frag.start, 'accept': frag.accept, 'transitions': dict(transitions)}
    return steps, final_nfa

# -------------------------
# Conversion NFA -> DFA
# -------------------------
def epsilon_closure(states, transitions):
    closure = set(states)
    stack = list(states)
    while stack:
        s = stack.pop()
        for sym, d in transitions.get(s, []):
            if sym == EPS and d not in closure:
                closure.add(d)
                stack.append(d)
    return closure

def move(states, symbol, transitions):
    result = set()
    for s in states:
        for sym, d in transitions.get(s, []):
            if sym == symbol:
                result.add(d)
    return result

def nfa_to_dfa(nfa):
    transitions = nfa['transitions']
    start = nfa['start']
    accept = nfa['accept']
    symbols = sorted(set(sym for lst in transitions.values() for sym,_ in lst if sym and sym != EPS))

    start_set = frozenset(epsilon_closure({start}, transitions))
    unmarked = [start_set]
    dfa_states = {start_set: 0}
    dfa_trans = {}
    dfa_accepts = set()
    if accept in start_set:
        dfa_accepts.add(start_set)

    sink = frozenset({'sink'})
    sink_needed = False
    while unmarked:
        T = unmarked.pop()
        for sym in symbols:
            Uset = epsilon_closure(move(T, sym, transitions), transitions)
            U = frozenset(Uset)
            if not U:
                sink_needed = True
                dfa_states.setdefault(sink, len(dfa_states))
                dfa_trans[(T, sym)] = sink
                continue
            if U not in dfa_states:
                dfa_states[U] = len(dfa_states)
                unmarked.append(U)
                if accept in U:
                    dfa_accepts.add(U)
            dfa_trans[(T, sym)] = U

    if sink_needed:
        for sym in symbols:
            dfa_trans[(sink, sym)] = sink

    return {'states': list(dfa_states.keys()), 'start': start_set, 'accepts': dfa_accepts, 'transitions': dfa_trans, 'symbols': symbols}

# -------------------------
# Minimisation DFA (Hopcroft) -> retourne nouvelle structure DFA minimale
# -------------------------
def minimize_dfa(dfa):
    states = list(dfa['states'])
    symbols = dfa['symbols']
    accepts = set(dfa['accepts'])
    non_accepts = set(states) - accepts

    # Initial partition
    P = []
    if accepts:
        P.append(frozenset(accepts))
    if non_accepts:
        P.append(frozenset(non_accepts))
    W = [p for p in P]

    # transition function mapping state->symbol->dest
    trans = {}
    for s in states:
        trans[s] = {}
        for sym in symbols:
            dest = dfa['transitions'].get((s, sym), None)
            trans[s][sym] = dest

    while W:
        A = W.pop()
        for c in symbols:
            # X = states that go to A on c
            X = set()
            for q in states:
                dest = trans[q].get(c, None)
                if dest in A:
                    X.add(q)
            newP = []
            for Y in P:
                inter = Y & X
                diff = Y - X
                if inter and diff:
                    newP.append(frozenset(inter))
                    newP.append(frozenset(diff))
                    if Y in W:
                        W.remove(Y)
                        W.append(frozenset(inter))
                        W.append(frozenset(diff))
                    else:
                        if len(inter) <= len(diff):
                            W.append(frozenset(inter))
                        else:
                            W.append(frozenset(diff))
                else:
                    newP.append(Y)
            P = newP

    # Build new DFA: each block in P is a state
    block_id = {b:i for i,b in enumerate(P)}
    new_states = list(P)
    new_start = None
    new_accepts = set()
    for b in new_states:
        if dfa['start'] in b:
            new_start = b
        if any(s in dfa['accepts'] for s in b):
            new_accepts.add(b)

    new_trans = {}
    for b in new_states:
        repr_state = next(iter(b))
        for sym in symbols:
            dest = dfa['transitions'].get((repr_state, sym), None)
            # dest might be None (sink absent), treat as unique sink block if needed
            if dest is None:
                # ignore (no transition)
                continue
            # find block containing dest
            for blk in new_states:
                if dest in blk:
                    new_trans[(b, sym)] = blk
                    break

    return {'states': new_states, 'start': new_start, 'accepts': new_accepts, 'transitions': new_trans, 'symbols': symbols}

# -------------------------
# Utility : build DOT (stable)
# -------------------------
def transitions_to_dot(transitions, new_edges=None, start=None, accept=None):
    g = graphviz.Digraph()
    g.attr(rankdir='LR', ranksep='1', nodesep='0.5')
    g.attr('node', shape='circle', fixedsize='true', width='1', height='1', fontsize='12')
    if start is not None:
        g.node('start', shape='point', width='0.1', height='0.1', fixedsize='true')
        g.edge('start', str(start))

    all_states = set(transitions.keys())
    # transitions keys may be (src,sym)->dest (for DFA) or src->list...
    # detect format: if values are lists -> NFA-style; else DFA-style
    sample = None
    for v in transitions.values():
        sample = v
        break

    if isinstance(sample, list) or sample is None:
        # NFA-style: transitions: {state: [(sym,dest), ...], ...}
        for s, lst in transitions.items():
            for _, d in lst:
                all_states.add(d)
        for s in sorted(all_states, key=lambda x: str(x)):
            if s == accept:
                g.node(str(s), shape='doublecircle')
            else:
                g.node(str(s))
        for s, lst in transitions.items():
            for sym, d in lst:
                color = "red" if new_edges and (s, sym, d) in new_edges else "black"
                label = EPS if sym == EPS or sym is None else str(sym)
                g.edge(str(s), str(d), label=label, color=color)
    else:
        # DFA-style: transitions: {(src,sym): dest, ...}
        nodes = set()
        for (src, sym), dest in transitions.items():
            nodes.add(src); nodes.add(dest)
        for s in sorted(nodes, key=lambda x: str(x)):
            if s == accept:
                g.node(str(s), shape='doublecircle')
            else:
                # display block/set nicely if it's a frozenset
                label = str(s)
                if isinstance(s, frozenset):
                    label = "{" + ",".join(map(str, sorted(s))) + "}"
                    if len(label) > 20:
                        label = label.replace(',', ',\n')
                g.node(str(s), label=label)
        for (src, sym), dest in transitions.items():
            label = EPS if sym == EPS or sym is None else str(sym)
            g.edge(str(src), str(dest), label=label)
    return g

# -------------------------
# Streamlit UI
# -------------------------
st.set_page_config(page_title="Algorithme de Thompson", layout="wide")

col_logo, col_title = st.columns([1,5])
with col_logo:
    try:
        st.image("logo.png", width=100)
    except:
        pass
with col_title:
    st.title("Algorithme de Thompson")
    st.caption("Construction de l’automate de Thompson et conversion NFA → DFA")

st.header("Entrée")
regex = st.text_input("Expression régulière", value="(a|b)*ab(a|b)*")

colA, colB, colC = st.columns([1,1,1])
with colA:
    build = st.button("Construire l'automate")
with colB:
    show_dfa = st.checkbox("Afficher le DFA (après NFA)", value=False)
with colC:
    show_min = st.checkbox("Afficher le DFA minimisé", value=False)

st.divider()

if 'steps' not in st.session_state:
    st.session_state.steps = []
if 'final_nfa' not in st.session_state:
    st.session_state.final_nfa = None
if 'idx' not in st.session_state:
    st.session_state.idx = 0
if 'last_postfix' not in st.session_state:
    st.session_state.last_postfix = ''

col1, col2 = st.columns([1,2])
postfix_box = col1.empty()
info_box = col1.empty()
graph_box = col2.empty()
nav1, nav2 = col1.columns([1,1])
prev_btn = nav1.button("← Étape précédente")
next_btn = nav2.button("Étape suivante")

if build:
    try:
        regex_expanded = expand_plus(regex.strip())
        regex2 = insert_concat(regex_expanded)
        postfix = to_postfix(regex2)
        steps, final_nfa = thompson_with_steps(postfix)
        st.session_state.steps = steps
        st.session_state.final_nfa = final_nfa
        st.session_state.idx = 0
        st.session_state.last_postfix = postfix
        st.success("Automate NFA construit.")
    except Exception as e:
        st.error(f"Erreur : {e}")
        st.session_state.steps = []
        st.session_state.final_nfa = None

if st.session_state.steps:
    if next_btn and st.session_state.idx < len(st.session_state.steps)-1:
        st.session_state.idx += 1
    if prev_btn and st.session_state.idx > 0:
        st.session_state.idx -= 1

    idx = st.session_state.idx
    step = st.session_state.steps[idx]
    postfix_box.markdown(f"**Étape {idx+1}/{len(st.session_state.steps)} — Symbole traité :** {step['tok']}")
    info_box.write(f"Pile : {step['stack']}")
    dot = transitions_to_dot(step['transitions'], step.get('new', []),
                             start=st.session_state.final_nfa['start'],
                             accept=st.session_state.final_nfa['accept'])
    graph_box.graphviz_chart(dot.source)

    # DFA original (non minimisé)
    if show_dfa and st.session_state.final_nfa:
        dfa = nfa_to_dfa(st.session_state.final_nfa)
        st.subheader("DFA correspondant (non minimisé)")
        gdfa = transitions_to_dot(dfa['transitions'], start=dfa['start'], accept=None)
        st.graphviz_chart(gdfa.source)

    # DFA minimisé
    if show_min and st.session_state.final_nfa:
        dfa = nfa_to_dfa(st.session_state.final_nfa)
        min_dfa = minimize_dfa(dfa)
        st.subheader("DFA minimisé")
        gmin = transitions_to_dot(min_dfa['transitions'], start=min_dfa['start'], accept=None)
        st.graphviz_chart(gmin.source)
else:
    st.info("Entrez une expression régulière et cliquez sur *Construire l'automate*.")
