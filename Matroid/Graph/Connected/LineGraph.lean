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

lemma connBetween_lineGraph_del_iff :
    (L(G) - F).SetConnected (E(G, s)) (E(G, t)) ↔ (G ＼ F).ConnectedBetween s t := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · -- If L(G) - F connects E(G,s) to E(G,t), then G ＼ F connects s to t
    -- Need to convert paths in line graph to paths in original graph
    sorry -- TODO: Convert paths in line graph to paths in original graph
  · -- If G ＼ F connects s to t, then L(G) - F connects E(G,s) to E(G,t)
    -- Need to convert paths in original graph to paths in line graph
    obtain ⟨P, hP, rfl, rfl⟩ := h.exists_isPath
    -- Convert path P in G to a path in L(G)
    sorry -- TODO: Convert paths in original graph to paths in line graph

-- TODO: Add lemmas for converting between paths in G and paths in L(G)
-- These will be needed to complete the Menger's theorem proof

end Graph
