import streamlit as st
from collections import defaultdict
import itertools
import graphviz
import re

EPS = 'ε'

def expand_plus(regex):
    pattern_group = re.compile(r'(\([^()]+\))\+')
    pattern_sym = re.compile(r'([A-Za-z0-9])\+')
    prev = None
    s = regex
    while prev != s:
        prev = s
        s = pattern_group.sub(r'\1.\1*', s)
        s = pattern_sym.sub(r'\1.\1*', s)
    return s

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
            transitions.setdefault(a, [])
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

# ----------- Minimize DFA avec noms I, II, III et transitions groupées ------------
def minimize_dfa_nice(dfa):
    # Partition initiale
    states = list(dfa['states'])
    symbols = dfa['symbols']
    accepts = set(dfa['accepts'])
    non_accepts = set(states) - accepts

    P = []
    if accepts:
        P.append(frozenset(accepts))
    if non_accepts:
        P.append(frozenset(non_accepts))
    W = [p for p in P]

    trans = {}
    for s in states:
        trans[s] = {}
        for sym in symbols:
            dest = dfa['transitions'].get((s, sym), None)
            trans[s][sym] = dest

    while W:
        A = W.pop()
        for c in symbols:
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

    new_states = list(P)
    new_start = None
    new_accepts = set()
    for b in new_states:
        if dfa['start'] in b:
            new_start = b
        if any(s in dfa['accepts'] for s in b):
            new_accepts.add(b)

    # Transitions groupées
    new_trans = {}
    for b in new_states:
        repr_state = next(iter(b))
        dest_map = defaultdict(list)
        for sym in symbols:
            dest = dfa['transitions'].get((repr_state, sym), None)
            for blk in new_states:
                if dest in blk:
                    dest_map[tuple(blk)].append(sym)
                    break
        for blk, syms in dest_map.items():
            new_trans[(b, ','.join(sorted(syms)))] = blk

    # Renommer les états I, II, III ...
    names = {}
    legend = {}
    roman = ["I","II","III","IV","V","VI","VII","VIII","IX","X","XI","XII","XIII","XIV","XV"]
    for i, s in enumerate(new_states):
        lab = roman[i] if i < len(roman) else f"X{i}"
        names[s] = lab
        legend[lab] = "{" + ",".join(str(x) for x in sorted(s)) + "}"

    return {'states': new_states, 'start': new_start, 'accepts': new_accepts, 'transitions': new_trans, 'symbols': symbols, 'names': names, 'legend': legend}

# ----------------- Graphique DFA minimisé nice ------------------
def build_dfa_graph_nice(dfa_min):
    g = graphviz.Digraph()
    g.attr(rankdir='LR', ranksep='1', nodesep='0.5')
    g.attr('node', shape='circle', fixedsize='true', width='1.5', height='1.5', fontsize='12')

    start = dfa_min['start']
    accept_set = dfa_min['accepts']
    names = dfa_min['names']
    legend = dfa_min['legend']

    g.node('start', shape='point', width='0.1', height='0.1', fixedsize='true')
    g.edge('start', names[start])

    for s in dfa_min['states']:
        shape = 'doublecircle' if s in accept_set else 'circle'
        g.node(names[s], label=names[s], shape=shape)

    for (src, syms), dest in dfa_min['transitions'].items():
        g.edge(names[src], names[dest], label=syms)

    return g, legend

# ----------------- Streamlit UI -----------------
st.set_page_config(page_title="Thompson DFA Minimized", layout="wide")

st.title("Algorithme de Thompson avec DFA minimisé")

regex = st.text_input("Expression régulière", value="(a|b)*ab(a|b)*")
build = st.button("Construire l'automate")
show_dfa = st.checkbox("Afficher DFA")
show_min = st.checkbox("Afficher DFA minimisé")

if 'final_nfa' not in st.session_state:
    st.session_state.final_nfa = None

if build:
    try:
        regex_expanded = expand_plus(regex.strip())
        regex2 = insert_concat(regex_expanded)
        postfix = to_postfix(regex2)
        _, final_nfa = thompson_with_steps(postfix)
        st.session_state.final_nfa = final_nfa
        st.success("NFA construit avec succès !")
    except Exception as e:
        st.error(f"Erreur : {e}")
        st.session_state.final_nfa = None

if st.session_state.final_nfa:
    nfa = st.session_state.final_nfa
    st.subheader("NFA")
    g_nfa = build_nfa_graph(nfa)
    st.graphviz_chart(g_nfa.source)

    if show_dfa:
        dfa = nfa_to_dfa(nfa)
        st.subheader("DFA")
        g, mapping, legend = build_dfa_graph(dfa)
        st.graphviz_chart(g.source)

    if show_min:
        dfa = nfa_to_dfa(nfa)
        min_dfa = minimize_dfa_nice(dfa)
        st.subheader("DFA minimisé (états I,II,III...)")
        g_min, legend_min = build_dfa_graph_nice(min_dfa)
        st.graphviz_chart(g_min.source)
        leg_lines = [f'- **{lab}** = `{content}`' for lab, content in legend_min.items()]
        st.markdown('<br>'.join(leg_lines), unsafe_allow_html=True)
