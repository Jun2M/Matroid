import Matroid.Graph.Connected.Basic
import Matroid.Graph.Connected.Set.Defs
import Matroid.Graph.Constructions.Basic

open Set Function Nat WList

variable {α β ι : Type*} {G H : Graph α β} {u v x x₁ x₂ y y₁ y₂ z s t : α}
  {e e' f g : β} {U V S T X Y : Set α} {F F' R R': Set β} {C W w P Q : WList α β} {n m : ℕ}

namespace Graph

instance [G.Finite] : L(G).Finite := by
  simp only [LineGraph_vertexSet]
  exact G.edgeSet_finite

@[simp]
lemma lineGraph_edgeDelete : L(G ＼ F) = L(G) - F := by
  ext a b c
  · simp only [LineGraph_vertexSet, edgeDelete_edgeSet, vertexDelete_vertexSet]
    rw [diff_eq_self]
    exact fun e he ↦ he.edge_mem
  · simp only [LineGraph_isLink, edgeDelete_isLink_iff, vertexDelete_isLink_iff, mem_diff]
    constructor
    · intro ⟨⟨x, he, hf⟩, hF⟩
      exact ⟨⟨x, by simpa using he, by simpa using hf⟩, fun h ↦ hF (by simpa using h)⟩
    · intro ⟨⟨x, he, hf⟩, hF⟩
      exact ⟨⟨x, by simpa using he, by simpa using hf⟩, fun h ↦ hF (by simpa using h)⟩

/-- Convert a path in G to a path in L(G) by taking the sequence of edges.
    The vertices of the L(G) path are the edges of the G path. -/
def lineGraph_pathMap (P : WList α β) (hP : G.IsPath P) (hne : P.Nonempty) : WList β (Sym2 β) :=
  match P with
  | nil x => 
    -- Single vertex path - pick an edge incident to it (must exist since hne)
    have ⟨e, he⟩ := hne.edgeSet_nonempty
    nil e
  | cons x e (nil y) => 
    -- Single edge path: just the edge
    nil e
  | cons x e (cons y f w) =>
    -- Multiple edges: e, f, ...
    -- In L(G): e -> f -> ... where e and f share vertex y
    -- Recursively build the rest
    have hw : G.IsPath (cons y f w) := by
      simp only [cons_isPath_iff] at hP ⊢
      exact ⟨hP.2.1, hP.2.2⟩
    have hne' : (cons y f w).Nonempty := ⟨y, by simp⟩
    cons e (Sym2.mk (e, f)) (lineGraph_pathMap (cons y f w) hw hne')

lemma IsPath.lineGraph_pathMap {P} (hP : G.IsPath P) (hne : P.Nonempty) :
    L(G).IsPath (lineGraph_pathMap P hP hne) := by
  match P with
  | nil x => 
    simp [lineGraph_pathMap]
    have ⟨e, he⟩ := hne.edgeSet_nonempty
    exact ⟨IsWalk.nil he.edge_mem, by simp⟩
  | cons x e (nil y) =>
    simp [lineGraph_pathMap]
    exact ⟨IsWalk.nil hP.isWalk.1.edge_mem, by simp⟩
  | cons x e (cons y f w) =>
    simp [lineGraph_pathMap]
    have hw : G.IsPath (cons y f w) := by
      simp only [cons_isPath_iff] at hP ⊢
      exact ⟨hP.2.1, hP.2.2⟩
    have hne' : (cons y f w).Nonempty := ⟨y, by simp⟩
    refine ⟨?_, ?_⟩
    · refine IsWalk.cons ?_ ?_
      · exact hw.lineGraph_pathMap hne'
      · -- Show e and f are adjacent in L(G)
        simp [lineGraph_adj_iff]
        use y
        -- e is incident to x and y, f is incident to y
        have h1 := hP.isWalk.1
        have h2 := (IsWalk.cons hP.isWalk.of_cons hP.isWalk.1).1
        exact ⟨h1.inc_right, h2.inc_left⟩
    · -- Show no repeated vertices (edges) - follows from P.edge.Nodup
      simp [cons_vertex, List.nodup_cons]
      constructor
      · -- First edge not in rest
        intro he'
        have := hP.edge_nodup
        simp [cons_edge, List.nodup_cons] at this
        exact this.1 he'
      · -- Rest has no duplicates
        have hw' : L(G).IsPath (lineGraph_pathMap (cons y f w) hw hne') := hw.lineGraph_pathMap hne'
        exact hw'.nodup

lemma lineGraph_pathMap_first {P} (hP : G.IsPath P) (hne : P.Nonempty) :
    (lineGraph_pathMap P hP hne).first = hne.firstEdge := by
  cases P with
  | nil => simp [lineGraph_pathMap, Nonempty.firstEdge]
  | cons x e w =>
    simp [lineGraph_pathMap, Nonempty.firstEdge_cons]

lemma lineGraph_pathMap_last {P} (hP : G.IsPath P) (hne : P.Nonempty) :
    (lineGraph_pathMap P hP hne).last = hne.lastEdge := by
  cases P with
  | nil => 
    simp [lineGraph_pathMap, Nonempty.lastEdge]
    have ⟨e, he⟩ := hne.edgeSet_nonempty
    simp [he]
  | cons x e w =>
    cases w with
    | nil => simp [lineGraph_pathMap, Nonempty.lastEdge_cons]
    | cons y f w' =>
      simp [lineGraph_pathMap]
      have hw : G.IsPath (cons y f w') := by
        simp only [cons_isPath_iff] at hP ⊢
        exact ⟨hP.2.1, hP.2.2⟩
      have hne' : (cons y f w').Nonempty := ⟨y, by simp⟩
      -- Last of recursive call equals lastEdge of the subpath
      have ih := lineGraph_pathMap_last hw hne'
      -- But we need lastEdge of the full path
      simp [Nonempty.lastEdge_cons] at hne ⊢
      rw [ih]
      -- lastEdge of cons x e (cons y f w') equals lastEdge of cons y f w'
      -- This follows from Nonempty.lastEdge_cons
      rfl

/-- Convert a path in L(G) back to a path in G by reconstructing vertices.
    The path in L(G) is a sequence of edges e₁, e₂, ..., eₙ where consecutive edges share a vertex.
    We reconstruct the vertex sequence. -/
def pathOfLineGraph [DecidableEq α] (P : WList β (Sym2 β)) (hP : L(G).IsPath P) 
    (he : P.first ∈ E(G, s)) (hf : P.last ∈ E(G, t)) : WList α β :=
  match P with
  | nil e =>
    -- Single edge e incident to s (and must also be incident to t since it's the last)
    have ⟨x, y, he'⟩ := exists_isLink_of_mem_edgeSet (by simpa using he)
    -- One of x, y is s, the other is t
    by_cases hsx : x = s
    · subst x
      exact cons s e (nil y)
    · -- Then y = s
      have hyt : y = t := by
        -- Since e is also incident to t and e connects x and y, and x ≠ s, we must have y = t
        sorry
      subst y
      exact cons t e (nil x)
  | cons e s_edge P' =>
    have hP' : L(G).IsPath P' := by simpa using hP.of_cons
    -- e is the first edge, incident to s
    -- s_edge is the Sym2 edge connecting e to P'.first
    -- P' is the rest
    have hadj : L(G).Adj e P'.first := by
      -- e and P'.first are connected by s_edge
      have := hP.1
      simp [cons_isWalk_iff] at this
      exact this.1
    simp [lineGraph_adj_iff] at hadj
    obtain ⟨x, he_inc, hf_inc⟩ := hadj
    -- e is incident to x, P'.first is incident to x
    -- e is also incident to s (since e ∈ E(G, s))
    have ⟨a, b, he_link⟩ := exists_isLink_of_mem_edgeSet (by simpa using he)
    -- One of a, b is s, the other is x (the shared vertex)
    have hf' : P'.last ∈ E(G, t) := hf  -- If P' is the whole path, its last is the last
    have P_rec := pathOfLineGraph P' hP' (by sorry) hf'
    -- Determine which vertex to use
    by_cases ha : a = s
    · subst a
      -- Then b = x (the shared vertex)
      have hbx : b = x := by sorry
      subst b
      exact cons s e P_rec
    · -- Then b = s
      have hbs : b = s := by sorry
      subst b
      have hax : a = x := by sorry
      subst a
      exact cons s e P_rec

lemma IsPath.pathOfLineGraph [DecidableEq α] (P : WList β (Sym2 β)) (hP : L(G).IsPath P)
    (he : P.first ∈ E(G, s)) (hf : P.last ∈ E(G, t)) :
    G.IsPath (pathOfLineGraph P hP he hf) := by
  match P with
  | nil e =>
    simp [pathOfLineGraph]
    -- Single edge path from s to t
    have ⟨x, y, he'⟩ := exists_isLink_of_mem_edgeSet (by simpa using he)
    by_cases hsx : x = s
    · subst x
      simp [pathOfLineGraph]
      exact ⟨IsWalk.cons (IsWalk.nil (by sorry)) he', by simp⟩
    · -- Then y = s, and we need to show x = t
      sorry
  | cons e s_edge P' =>
    simp [pathOfLineGraph]
    have hP' : L(G).IsPath P' := by simpa using hP.of_cons
    -- Recursive case
    sorry -- Need to show the reconstructed path is valid

lemma pathOfLineGraph_first [DecidableEq α] (P : WList β (Sym2 β)) (hP : L(G).IsPath P)
    (he : P.first ∈ E(G, s)) (hf : P.last ∈ E(G, t)) :
    (pathOfLineGraph P hP he hf).first = s := by
  match P with
  | nil e => 
    simp [pathOfLineGraph]
    have ⟨x, y, he'⟩ := exists_isLink_of_mem_edgeSet (by simpa using he)
    by_cases hsx : x = s
    · subst x; simp
    · -- Then y = s
      sorry
  | cons e s_edge P' =>
    simp [pathOfLineGraph]
    sorry

lemma pathOfLineGraph_last [DecidableEq α] (P : WList β (Sym2 β)) (hP : L(G).IsPath P)
    (he : P.first ∈ E(G, s)) (hf : P.last ∈ E(G, t)) :
    (pathOfLineGraph P hP he hf).last = t := by
  match P with
  | nil e =>
    simp [pathOfLineGraph]
    -- Single edge: both endpoints determined by he and hf
    sorry
  | cons e s_edge P' =>
    simp [pathOfLineGraph]
    -- Last of recursive call equals t
    have hP' : L(G).IsPath P' := by simpa using hP.of_cons
    have ih := pathOfLineGraph_last P' hP' (by sorry) hf
    rw [ih]
    -- But we need to show the last vertex of the full reconstructed path is t
    sorry

/-- Convert a SetEnsemble in L(G) to a VertexEnsemble in G with edge-disjoint property. -/
def vertexEnsembleOfSetEnsemble [DecidableEq α] (A : L(G).SetEnsemble) 
    (hA : A.between (E(G, s)) (E(G, t))) : G.VertexEnsemble s t (A.paths) where
  f P := pathOfLineGraph P (A.valid P.prop).isPath 
    (hA P.prop).first_mem (hA P.prop).last_mem
  isPath P := (A.valid P.prop).isPath.pathOfLineGraph 
    (hA P.prop).first_mem (hA P.prop).last_mem
  first_eq P := pathOfLineGraph_first P (A.valid P.prop).isPath 
    (hA P.prop).first_mem (hA P.prop).last_mem
  last_eq P := pathOfLineGraph_last P (A.valid P.prop).isPath 
    (hA P.prop).first_mem (hA P.prop).last_mem
  internallyDisjoint P Q hne := by
    -- Vertex-disjoint paths in L(G) become edge-disjoint paths in G
    ext x
    simp only [mem_inter_iff, mem_vertexSet_iff]
    -- If paths share a vertex in G, they must share an edge, which contradicts vertex-disjointness in L(G)
    sorry -- TODO: Show vertex-disjoint in L(G) implies edge-disjoint in G

lemma vertexEnsembleOfSetEnsemble_edgeDisjoint [DecidableEq α] (A : L(G).SetEnsemble)
    (hA : A.between (E(G, s)) (E(G, t))) :
    (vertexEnsembleOfSetEnsemble A hA).edgeDisjoint := by
  rintro P Q hne
  -- Paths in L(G) are vertex-disjoint (they share no edges as vertices)
  -- This means the corresponding paths in G are edge-disjoint
  have hdj := A.disjoint P.prop Q.prop hne
  -- Convert to edge-disjointness in G
  sorry -- TODO: Show vertex-disjoint in L(G) implies edge-disjoint in G

/-- Convert a VertexEnsemble in G with edge-disjoint property to a SetEnsemble in L(G). -/
def setEnsembleOfVertexEnsemble (A : G.VertexEnsemble s t ι) (hA : A.edgeDisjoint) :
    L(G).SetEnsemble where
  paths := {P | ∃ i, lineGraph_pathMap (A.f i) (A.isPath i) (by simp : (A.f i).Nonempty) = P}
  disjoint P Q hP hQ hne := by
    obtain ⟨i, rfl⟩ := hP
    obtain ⟨j, rfl⟩ := hQ
    -- Edge-disjoint paths in G become vertex-disjoint paths in L(G)
    by_cases hij : i = j
    · subst hij
      contradiction
    · -- Paths are edge-disjoint, so their line graph representations are vertex-disjoint
      have hdj := hA hij
      -- Convert edge-disjoint to vertex-disjoint
      sorry -- TODO: Show edge-disjoint in G implies vertex-disjoint in L(G)
  valid P := by
    obtain ⟨i, rfl⟩ := P
    exact (A.isPath i).lineGraph_pathMap (by simp : (A.f i).Nonempty)

lemma setEnsembleOfVertexEnsemble_between (A : G.VertexEnsemble s t ι) (hA : A.edgeDisjoint) :
    (setEnsembleOfVertexEnsemble A hA).between (E(G, s)) (E(G, t)) := by
  intro P hP
  obtain ⟨i, rfl⟩ := hP
  refine ⟨?_, ?_⟩
  · -- First edge is in E(G, s)
    rw [lineGraph_pathMap_first]
    -- firstEdge of A.f i is incident to s = (A.f i).first
    have hfirst : (by simp : (A.f i).Nonempty).firstEdge ∈ E(G, s) := by
      simp [mem_incEdges_iff]
      use (A.f i).first
      rw [A.first_eq i]
      exact ⟨by simp, (A.isPath i).isWalk.edge_mem_of_mem (by simp)⟩
    exact hfirst
  · -- Last edge is in E(G, t)
    rw [lineGraph_pathMap_last]
    -- lastEdge of A.f i is incident to t = (A.f i).last
    have hlast : (by simp : (A.f i).Nonempty).lastEdge ∈ E(G, t) := by
      simp [mem_incEdges_iff]
      use (A.f i).last
      rw [A.last_eq i]
      -- Need to show lastEdge is incident to last vertex
      sorry -- TODO: Show lastEdge is incident to last vertex
    exact hlast

lemma connBetween_lineGraph_del_iff :
    (L(G) - F).SetConnected (E(G, s)) (E(G, t)) ↔ (G ＼ F).ConnectedBetween s t := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · -- If L(G) - F connects E(G,s) to E(G,t), then G ＼ F connects s to t
    obtain ⟨P, hP⟩ := h.exists_isPathFrom
    classical
    -- P is a path from some edge in E(G,s) to some edge in E(G,t)
    obtain ⟨e, he, heP⟩ := hP.first_mem
    obtain ⟨f, hf, hfP⟩ := hP.last_mem
    -- Convert to path in G
    use pathOfLineGraph P hP.isPath he hf
    exact ⟨hP.isPath.pathOfLineGraph he hf, pathOfLineGraph_first P hP.isPath he hf,
      pathOfLineGraph_last P hP.isPath he hf⟩
  · -- If G ＼ F connects s to t, then L(G) - F connects E(G,s) to E(G,t)
    obtain ⟨P, hP, rfl, rfl⟩ := h.exists_isPath
    -- Convert path P in G to a path in L(G)
    have hne : P.Nonempty := ⟨P.first, by simp⟩
    use lineGraph_pathMap P hP hne, hP.lineGraph_pathMap hne
    · -- Show first edge is in E(G, s)
      rw [lineGraph_pathMap_first]
      have hfirst : hne.firstEdge ∈ E(G, s) := by
        simp [mem_incEdges_iff]
        use P.first
        exact ⟨by simp, hP.isWalk.edge_mem_of_mem (by simp)⟩
      exact hfirst
    · -- Show last edge is in E(G, t)
      rw [lineGraph_pathMap_last]
      have hlast : hne.lastEdge ∈ E(G, t) := by
        simp [mem_incEdges_iff]
        use P.last
        -- lastEdge is incident to last vertex by path structure
        have hmem : hne.lastEdge ∈ P.edge := hne.lastEdge_mem
        obtain ⟨x, y, hdInc⟩ := exists_dInc_of_mem_edge hmem
        -- For a path, the last edge connects to the last vertex
        -- This follows from the alternating structure
        cases P with
        | nil => simp at hmem
        | cons u e w =>
          -- The last edge in the sequence connects to P.last
          -- We can show this by induction or by using the path structure
          by_cases hylast : y = P.last
          · subst y
            exact hdInc.inc_right
          · -- Then x = P.last (since it's the last edge)
            -- This requires showing the path structure forces this
            sorry -- This follows from path structure - last edge's endpoint is last vertex
      exact hlast

end Graph
