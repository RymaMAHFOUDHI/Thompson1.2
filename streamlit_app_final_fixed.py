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

def minimize_dfa(dfa):
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

    new_trans = {}
    for b in new_states:
        repr_state = next(iter(b))
        for sym in symbols:
            dest = dfa['transitions'].get((repr_state, sym), None)
            if dest is None:
                continue
            for blk in new_states:
                if dest in blk:
                    new_trans[(b, sym)] = blk
                    break

    return {'states': new_states, 'start': new_start, 'accepts': new_accepts, 'transitions': new_trans, 'symbols': symbols}

def abbreviate(states):
    mapping = {}
    legend = {}
    for i, s in enumerate(states):
        base = chr(ord('A') + (i % 26))
        suffix = str(i // 26) if i // 26 > 0 else ''
        lab = base + suffix
        mapping[s] = lab
        if isinstance(s, frozenset):
            content = "{" + ",".join(map(str, sorted(s))) + "}"
        else:
            content = str(s)
        legend[lab] = content
    return mapping, legend

def build_nfa_graph(nfa, new_edges=None):
    g = graphviz.Digraph()
    g.attr(rankdir='LR', ranksep='1', nodesep='0.5')
    g.attr('node', shape='circle', fixedsize='true', width='1', height='1', fontsize='12')

    transitions = nfa['transitions']
    start = nfa['start']
    accept = nfa['accept']

    g.node('start', shape='point', width='0.1', height='0.1', fixedsize='true')
    g.edge('start', f"n{start}")

    all_states = set(transitions.keys())
    for s, lst in transitions.items():
        for _, d in lst:
            all_states.add(d)

    for s in sorted(all_states, key=lambda x: int(str(x)) if str(x).isdigit() else str(x)):
        shape = 'doublecircle' if s == accept else 'circle'
        color = 'red' if s == start else 'black'
        g.node(f"n{s}", label=str(s), shape=shape, color=color, width='1', height='1', fixedsize='true')

    for s, lst in transitions.items():
        for sym, d in lst:
            label = EPS if sym == EPS or sym is None else str(sym)
            color = "red" if new_edges and (s, sym, d) in new_edges else "black"
            g.edge(f"n{s}", f"n{d}", label=label, color=color)

    return g

def build_dfa_graph(dfa, abbreviate_names=True):
    states = dfa['states']
    mapping, legend = abbreviate(states) if abbreviate_names else ({s: ("{" + ",".join(map(str, sorted(s))) + "}") for s in states}, {})
    g = graphviz.Digraph()
    g.attr(rankdir='LR', ranksep='1', nodesep='0.5')
    g.attr('node', shape='circle', fixedsize='true', width='1.2', height='1.2', fontsize='12')
    start = dfa['start']
    accept_set = set(dfa['accepts'])
    g.node('start', shape='point', width='0.1', height='0.1', fixedsize='true')
    start_id = mapping.get(start, str(start))
    g.edge('start', start_id)
    for s in states:
        nid = mapping.get(s, str(s))
        label = nid
        shape = 'doublecircle' if s in accept_set else 'circle'
        g.node(nid, label=label, shape=shape, width='1.2', height='1.2', fixedsize='true')
    for (src, sym), dest in dfa['transitions'].items():
        src_id = mapping.get(src, str(src))
        dest_id = mapping.get(dest, str(dest))
        lab = EPS if sym == EPS or sym is None else str(sym)
        g.edge(src_id, dest_id, label=lab)
    return g, mapping, legend

# ---------- Streamlit UI ----------
st.set_page_config(page_title="Algorithme de Thompson (abrégé)", layout="wide")

col_logo, col_title = st.columns([1,5])
with col_logo:
    try:
        st.image("logo.png", width=100)
    except:
        pass
with col_title:
    st.title("Algorithme de Thompson")
    st.caption("Construction NFA → DFA (noms abrégés + légende)")

st.header("Entrée")
regex = st.text_input("Expression régulière", value="(a|b)*ab(a|b)*")

colA, colB, colC = st.columns([1,1,1])
with colA:
    build = st.button("Construire l'automate")
with colB:
    show_dfa = st.checkbox("Afficher le DFA (après NFA)", value=True)
with colC:
    show_min = st.checkbox("Afficher le DFA minimisé", value=False)

st.divider()

if 'steps' not in st.session_state:
    st.session_state.steps = []
if 'final_nfa' not in st.session_state:
    st.session_state.final_nfa = None
if 'idx' not in st.session_state:
    st.session_state.idx = 0

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

    temp_nfa = {
        'start': st.session_state.final_nfa['start'],
        'accept': st.session_state.final_nfa['accept'],
        'transitions': step['transitions']
    }
    dot_nfa = build_nfa_graph(temp_nfa, step.get('new', []))
    graph_box.graphviz_chart(dot_nfa.source)

    if show_dfa and st.session_state.final_nfa:
        dfa = nfa_to_dfa(st.session_state.final_nfa)
        st.subheader("DFA correspondant (états abrégés)")
        gdfa, mapping, legend = build_dfa_graph(dfa, abbreviate_names=True)
        st.graphviz_chart(gdfa.source)
        leg_lines = [f'- **{lab}** = `{content}`' for lab, content in legend.items()]
        st.markdown('\\n'.join(leg_lines))

    if show_min and st.session_state.final_nfa:
        dfa = nfa_to_dfa(st.session_state.final_nfa)
        min_dfa = minimize_dfa(dfa)
        st.subheader("DFA minimisé (états abrégés)")
        gmin, m_mapping, m_legend = build_dfa_graph(min_dfa, abbreviate_names=True)
        st.graphviz_chart(gmin.source)
        leg_lines = [f'- **{lab}** = `{content}`' for lab, content in m_legend.items()]
        st.markdown('\\n'.join(leg_lines))
else:
    st.info("Entrez une expression régulière et cliquez sur *Construire l'automate*.")
