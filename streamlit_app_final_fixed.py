import streamlit as st
import graphviz

# ---------- CONFIG PAGE ----------
st.set_page_config(page_title="Algorithme de Thompson", layout="wide", page_icon="🧩")

# ---------- HEADER ----------
col_logo, col_title = st.columns([1,6], gap="small")
with col_logo:
    try:
        st.image("logo.png", width=160)  # logo agrandi
    except:
        pass
with col_title:
    st.markdown("<h1 style='margin-bottom:0px; margin-top:0px;'>Algorithme de Thompson</h1>", unsafe_allow_html=True)
    st.caption("Transformation pas à pas : NFA → DFA → DFA minimisé")

# ---------- STYLE ----------
st.markdown("""
<style>
div[data-testid="stHorizontalBlock"] div[data-testid="stButton"] {text-align: center; display: flex; justify-content: center;}
h1, h2, h3, h4 {text-align: center;}
</style>
""", unsafe_allow_html=True)

# ---------- DÉFINITION GRAPHE MULTISYMBOLE ----------
def build_graph_multisym(auto, start_key='start', accept_key='accept', transitions_key='transitions', title=None, enlarge=False):
    dot = graphviz.Digraph()
    dot.attr(rankdir='LR', size='8,5')

    if enlarge:
        dot.attr('node', shape='circle', fontsize='22', width='1.2', height='1.2')
    else:
        dot.attr('node', shape='circle', fontsize='18')

    start = auto[start_key]
    accept = auto[accept_key]
    transitions = auto[transitions_key]

    # Regrouper transitions multi-symboles
    merged = {}
    for (src, sym), dests in transitions.items():
        if isinstance(dests, list):
            for d in dests:
                merged.setdefault((src, d), set()).add(sym)
        else:
            merged.setdefault((src, dests), set()).add(sym)

    for s in {src for (src, _) in merged.keys()} | {d for (_, d) in merged.keys()}:
        if s == start:
            dot.node(str(s), str(s), color='red', penwidth='3')  # état initial bord rouge
        elif s in accept if isinstance(accept, list) else [accept]:
            dot.node(str(s), str(s), peripheries='2', color='green')
        else:
            dot.node(str(s), str(s))

    for (src, dest), syms in merged.items():
        dot.edge(str(src), str(dest), label=",".join(sorted(syms)))

    if title:
        dot.attr(label=title, labelloc='t', fontsize='24')

    return dot

# ---------- EXEMPLE SIMULÉ ----------
# NFA (agrandi)
nfa = {
    'start': 'q0',
    'accept': ['q2'],
    'transitions': {
        ('q0', 'a'): ['q0', 'q1'],
        ('q1', 'b'): ['q2']
    }
}

# DFA renommé A,B,C
dfa = {
    'start': 'A',
    'accept': ['C'],
    'transitions': {
        ('A', 'a'): 'B',
        ('B', 'a'): 'B',
        ('B', 'b'): 'C'
    }
}

# DFA minimisé renommé I,II,III
min_dfa = {
    'start': 'I',
    'accept': ['III'],
    'transitions': {
        ('I', 'a'): 'II',
        ('II', 'a'): 'II',
        ('II', 'b'): 'III'
    },
    'legend': {'I': '{A}', 'II': '{B}', 'III': '{C}'}
}

# ---------- INTERFACE ----------
if "step" not in st.session_state:
    st.session_state.step = 0

col_prev, col_next = st.columns([1,1], gap="medium")
with col_prev:
    if st.button("⬅️ Étape précédente") and st.session_state.step > 0:
        st.session_state.step -= 1
with col_next:
    if st.button("Étape suivante ➡️") and st.session_state.step < 2:
        st.session_state.step += 1

step = st.session_state.step

# Centrer le graphe
st.markdown("<div style='text-align:center;'>", unsafe_allow_html=True)

if step == 0:
    st.subheader("NFA obtenu (agrandi)")
    g_nfa = build_graph_multisym(nfa, enlarge=True)
    st.graphviz_chart(g_nfa)
elif step == 1:
    st.subheader("Automate déterministe (DFA)")
    g_dfa = build_graph_multisym(dfa)
    st.graphviz_chart(g_dfa)
elif step == 2:
    st.subheader("Automate minimisé (DFA minimal)")
    g_min = build_graph_multisym(min_dfa)
    st.graphviz_chart(g_min)
    legend_text = "Légende : " + ", ".join(f"{k}={v}" for k,v in min_dfa['legend'].items())
    st.markdown(f"<p style='text-align:center;font-size:18px;'><b>{legend_text}</b></p>", unsafe_allow_html=True)

st.markdown("</div>", unsafe_allow_html=True)
