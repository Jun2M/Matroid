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

-- Helper lemma: vertex set of lineGraph_pathMap equals edge set of original path
lemma lineGraph_pathMap_vertex_eq_edge {P} (hP : G.IsPath P) (hne : P.Nonempty) :
    (lineGraph_pathMap P hP hne).vertex = P.edge := by
  cases P with
  | nil => 
    simp [lineGraph_pathMap]
    have ⟨e, he⟩ := hne.edgeSet_nonempty
    simp [he]
  | cons x e w =>
    cases w with
    | nil => simp [lineGraph_pathMap, cons_edge]
    | cons y f w' =>
      simp [lineGraph_pathMap, cons_vertex, cons_edge]
      have hw : G.IsPath (cons y f w') := by
        simp only [cons_isPath_iff] at hP ⊢
        exact ⟨hP.2.1, hP.2.2⟩
      have hne' : (cons y f w').Nonempty := ⟨y, by simp⟩
      have ih := lineGraph_pathMap_vertex_eq_edge hw hne'
      rw [ih]
      simp [List.cons_append]

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
    -- Single edge e incident to both s and t
    have ⟨x, y, he'⟩ := exists_isLink_of_mem_edgeSet (by simpa using he)
    -- Since e ∈ E(G, s) and e ∈ E(G, t), and e connects x and y, we have {s, t} = {x, y}
      have hst : s = x ∧ t = y ∨ s = y ∧ t = x := by
        -- e is incident to s, so s ∈ {x, y}
        have hs_xy : s = x ∨ s = y := by
          have := he' : G.IsLink e x y
          exact (this.left_mem.eq_or_eq_of_inc he).imp id (this.right_mem.eq_or_eq_of_inc he)
        -- e is also incident to t (from hf)
        have ht_inc : G.Inc e t := by simpa [mem_incEdges_iff] using hf
        have ht_xy : t = x ∨ t = y := by
          have := he' : G.IsLink e x y
          exact (this.left_mem.eq_or_eq_of_inc ht_inc).imp id (this.right_mem.eq_or_eq_of_inc ht_inc)
        -- Combine: if s = x then t = y, if s = y then t = x
        obtain (rfl | rfl) := hs_xy
        · obtain (rfl | rfl) := ht_xy
          · -- s = x, t = x means s = t - handle separately
            sorry
          · exact Or.inl ⟨rfl, rfl⟩
        · obtain (rfl | rfl) := ht_xy
          · exact Or.inr ⟨rfl, rfl⟩
          · -- s = y, t = y means s = t
            sorry
    obtain (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) := hst
    · exact cons s e (nil t)
    · exact cons t e (nil s)
  | cons e s_edge P' =>
    have hP' : L(G).IsPath P' := by simpa using hP.of_cons
    -- e is the first edge, incident to s
    -- e and P'.first are adjacent (share a vertex x)
    have hadj : L(G).Adj e P'.first := by
      have := hP.1
      simp [cons_isWalk_iff] at this
      exact this.1
    simp [lineGraph_adj_iff] at hadj
    obtain ⟨x, he_inc, hf_inc⟩ := hadj
    -- e is incident to both s and x
    -- Determine which endpoint of e is s
    have ⟨a, b, he_link⟩ := exists_isLink_of_mem_edgeSet (by simpa using he)
    -- One of a, b is s, the other is x
    have hs_ab : s = a ∨ s = b := by
      have := he_link : G.IsLink e a b
      exact (this.left_mem.eq_or_eq_of_inc he_inc).imp id (this.right_mem.eq_or_eq_of_inc he_inc)
    -- P'.first is incident to x, so we can recurse
    have hf' : P'.last ∈ E(G, t) := hf
    have hfirst' : P'.first ∈ E(G, x) := by
      simp [mem_incEdges_iff]
      use x
      exact ⟨hf_inc, by simpa using hP'.first_mem⟩
    have P_rec := pathOfLineGraph P' hP' hfirst' hf'
    -- Build the full path: s --e--> x --P'--> t
    obtain (rfl | rfl) := hs_ab
    · -- s = a, so b = x (the shared vertex)
      have hbx : b = x := by
        -- Since e connects a and b where a = s, and e is incident to x, we have b = x
        -- This follows from the fact that e is incident to both s and x, and e connects s and b
        have := he_link : G.IsLink e s b
        have hsx : s = x ∨ G.IsLink e s x := Inc.eq_or_isLink_of_inc he hf_inc
        obtain rfl | hlink := hsx
        · -- s = x, but then the path would be trivial (e connects s to itself)
          sorry -- Need to handle or exclude this case
        · -- e connects s and x, and e connects s and b, so b = x
          exact (this.eq_or_eq_of_isLink hlink).resolve_left (by sorry)
      subst b
      exact cons s e P_rec
    · -- s = b, so a = x
      have hax : a = x := by
        have := he_link : G.IsLink e a s
        have hsx : s = x ∨ G.IsLink e s x := Inc.eq_or_isLink_of_inc he hf_inc
        obtain rfl | hlink := hsx
        · sorry
        · exact (this.symm.eq_or_eq_of_isLink hlink).resolve_left (by sorry)
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
    -- This follows from the fact that vertices in L(G) are edges in G
    sorry -- TODO: Show vertex-disjoint in L(G) implies edge-disjoint in G

lemma vertexEnsembleOfSetEnsemble_edgeDisjoint [DecidableEq α] (A : L(G).SetEnsemble)
    (hA : A.between (E(G, s)) (E(G, t))) :
    (vertexEnsembleOfSetEnsemble A hA).edgeDisjoint := by
  rintro P Q hne
  -- Paths in L(G) are vertex-disjoint (they share no edges as vertices)
  -- This means the corresponding paths in G are edge-disjoint
  have hdj := A.disjoint P.prop Q.prop hne
  -- The paths in L(G) are vertex-disjoint, meaning they share no vertices
  -- Since vertices in L(G) are edges in G, this means the paths in G share no edges
  -- So they are edge-disjoint
  ext e
  simp only [mem_inter_iff, mem_edgeSet_iff]
  constructor
    · intro ⟨heP, heQ⟩
      -- e appears in both paths in G
      -- The line graph paths are the images of these paths under lineGraph_pathMap
      -- e is a vertex in both L(G) paths (since it's an edge in both G paths)
      -- But paths in L(G) are vertex-disjoint, contradiction
      have hP := vertexEnsembleOfSetEnsemble A hA
      have hQ := vertexEnsembleOfSetEnsemble A hA
      -- e is in the edge set of both reconstructed paths
      -- By lineGraph_pathMap_vertex_eq_edge, e is in the vertex set of both L(G) paths
      have heP' : e ∈ P.vertex := by
        -- P is a path in L(G), and we need to show e is in its vertex set
        -- This follows from the fact that pathOfLineGraph reconstructs the path
        sorry -- Need inverse relationship: edge set of pathOfLineGraph equals vertex set of L(G) path
      have heQ' : e ∈ Q.vertex := by sorry
      -- But paths are vertex-disjoint
      have hdj' := hdj
      rw [← hdj'] at heP'
      exact heP' heQ'
  · tauto

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
      -- Edge-disjoint paths in G have no common edges
      -- In L(G), edges of G become vertices, so vertex-disjointness follows
      ext e
      simp only [mem_inter_iff, mem_vertexSet_iff]
      constructor
      · intro ⟨heP, heQ⟩
        -- e is a vertex in both L(G) paths
        -- This means e is an edge in both G paths (A.f i and A.f j)
        -- But paths are edge-disjoint, contradiction
        have heP' : e ∈ (A.f i).edge := by
          -- e is in the line graph path's vertex set
          -- By lineGraph_pathMap_vertex_eq_edge, this equals the original path's edge set
          have hmap := lineGraph_pathMap_vertex_eq_edge (A.isPath i) (by simp : (A.f i).Nonempty)
          rw [← hmap] at heP
          exact heP
        have heQ' : e ∈ (A.f j).edge := by
          have hmap := lineGraph_pathMap_vertex_eq_edge (A.isPath j) (by simp : (A.f j).Nonempty)
          rw [← hmap] at heQ
          exact heQ
        -- But paths are edge-disjoint
        have hdj' := hdj
        rw [← hdj'] at heP'
        exact heP' heQ'
      · tauto
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
      -- Use the fact that any path can be written as dropLast.concat lastEdge last
      have hne : (A.f i).Nonempty := by simp
      have hconcat := hne.concat_dropLast
      have hdInc := dInc_concat (A.f i).dropLast hne.lastEdge (A.f i).last
      rw [← hconcat] at hdInc
      -- This gives us that lastEdge is incident to last vertex
      exact hdInc.inc_right
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
        -- Use the fact that P = P.dropLast.concat lastEdge last
        have hconcat := hne.concat_dropLast
        -- From dInc_concat, we know (P.dropLast.concat lastEdge last).DInc lastEdge (P.dropLast.last) last
        have hdInc := dInc_concat P.dropLast hne.lastEdge P.last
        rw [← hconcat] at hdInc
        -- So P.DInc lastEdge (P.dropLast.last) P.last
        -- This means lastEdge is incident to P.last (the right endpoint)
        exact hdInc.inc_right
      exact hlast

end Graph
