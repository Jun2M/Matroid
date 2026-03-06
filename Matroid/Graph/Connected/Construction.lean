import Matroid.ForMathlib.Card
import Matroid.Graph.Connected.Defs
import Matroid.Graph.Connected.Menger

open Set Function Nat WList

variable {α β : Type*} {G H K : Graph α β} {s t u v x x₁ x₂ y y₁ y₂ z : α} {n m : ℕ}
  {e e' f g : β} {U V S S' T T' X Y : Set α} {F F' R R': Set β} {C W P Q : WList α β}

@[simp]
lemma Set.pair_subsingleton_iff {x y : α} : ({x, y} : Set α).Subsingleton ↔ x = y := by
  refine ⟨fun h => h (by simp) (by simp), ?_⟩
  rintro rfl
  simp

namespace Graph

example (n : ℕ) : (⊥ : Graph α β).PreconnGE n := by simp

instance completeBipartiteGraph_finite (m n : ℕ) : (CompleteBipartiteGraph m n).Finite where
  vertexSet_finite := by
    rw [show V(CompleteBipartiteGraph m n) = Sum.inl '' Set.Iio m ∪ Sum.inr '' Set.Iio n by
      ext x
      cases x <;> simp [CompleteBipartiteGraph]]
    exact (Set.finite_Iio m).image Sum.inl |>.union <| (Set.finite_Iio n).image Sum.inr
  edgeSet_finite := by
    rw [show E(CompleteBipartiteGraph m n) = Set.Iio m ×ˢ Set.Iio n by
      ext e
      simp [CompleteBipartiteGraph]]
    exact (Set.finite_Iio m).prod <| Set.finite_Iio n

lemma edgeConnBetweenGE_of_pathFamily {ι : Type*} (f : ι → WList α β)
    (hPath : ∀ i, G.IsPath (f i)) (hFirst : ∀ i, (f i).first = s) (hLast : ∀ i, (f i).last = t)
    (hEdge : Pairwise (Disjoint on WList.edgeSet on f)) (hι : ENat.card ι = n) :
    G.EdgeConnBetweenGE s t n := by
  classical
  have hιFin : Finite ι := ENat.card_lt_top.mp <| hι ▸ ENat.coe_lt_top n
  intro F hF
  have hmeet : ∀ i, ∃ e ∈ E(f i), e ∈ F := by
    intro i
    have hF' : G.IsEdgeCutBetween F (f i).first (f i).last := by
      simpa [hFirst i, hLast i] using hF
    exact (hPath i).isWalk.exists_mem_isEdgeCutBetween hF'
  choose e heFpath heF using hmeet
  let g : ι → F := fun i ↦ ⟨e i, heF i⟩
  have hg : Injective g := by
    intro i j hij
    by_contra hne
    have hval : e i = e j := congrArg Subtype.val hij
    have hdisj : Disjoint E(f i) E(f j) := hEdge hne
    rw [Set.disjoint_left] at hdisj
    exact hdisj (heFpath i) (by simpa [hval] using heFpath j)
  have hcard : ENat.card ι ≤ F.encard := by
    simpa [ENat.card_coe_set_eq] using ENat.card_le_card_of_injective hg
  simpa [hι] using hcard

lemma edgeConnBetweenGE_of_edgeDisjoint {ι : Type*} (A : G.VertexEnsemble s t ι)
    (hA : A.edgeDisjoint) (hι : ENat.card ι = n) : G.EdgeConnBetweenGE s t n := by
  exact edgeConnBetweenGE_of_pathFamily A.f A.isPath A.first_eq A.last_eq hA hι

lemma IsEdgeCutBetween.symm (h : G.IsEdgeCutBetween F s t) : G.IsEdgeCutBetween F t s where
  subset_edgeSet := h.subset_edgeSet
  not_connBetween := by simpa [connBetween_comm] using h.not_connBetween

lemma EdgeConnBetweenGE.symm (h : G.EdgeConnBetweenGE s t n) : G.EdgeConnBetweenGE t s n := by
  intro F hF
  exact h hF.symm

private lemma fin3_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  have hi : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 := by omega
  rcases hi with hi | hi
  · exact Or.inl (Fin.ext hi)
  rcases hi with hi | hi
  · exact Or.inr <| Or.inl (Fin.ext hi)
  exact Or.inr <| Or.inr (Fin.ext hi)

@[simp]
lemma noEdge_isComplete_iff : (Graph.noEdge X β).IsComplete ↔ X.Subsingleton := by
  refine ⟨fun h x hx y hy => ?_, fun h x hx y hy hne => (hne <| h hx hy).elim⟩
  by_contra! hne
  obtain ⟨e, he⟩ := h x hx y hy hne
  simpa using he.edge_mem

@[simp]
lemma IsWalk.nil_of_noEdge (h : (Graph.noEdge X β).IsWalk W) : W.Nil := by
  match W with
  | .nil u => simp
  | .cons u e w => simp at h

@[simp]
lemma connBetween_noEdge_iff : (Graph.noEdge X β).ConnBetween x y ↔ x = y ∧ x ∈ X := by
  refine ⟨?_, ?_⟩
  · rintro ⟨w, hw, rfl, rfl⟩
    match hw.nil_of_noEdge with | .nil x => simp_all
  rintro ⟨rfl, hx⟩
  simpa

@[simp]
lemma noEdge_preconnected_iff : (Graph.noEdge X β).Preconnected ↔ X.Subsingleton := by
  refine ⟨fun h => ?_, fun h x y hx hy => ?_⟩
  · by_contra! ht
    obtain ⟨x, hx, y, hy, hne⟩ := ht
    simpa [hne] using h x y hx hy
  simp only [noEdge_vertexSet] at hx hy
  obtain rfl := h hx hy
  simpa

@[simp]
lemma noEdge_connected_iff : (Graph.noEdge X β).Connected ↔ ∃ v, X = {v} := by
  rw [connected_iff, noEdge_preconnected_iff, noEdge_vertexSet]
  simp only [exists_eq_singleton_iff_nonempty_subsingleton]

@[simp]
lemma IsSepBetween.ne_of_noEdge (h : (Graph.noEdge X β).IsSepBetween x y Y) (hx : x ∈ X) :
    x ≠ y := by
  rintro rfl
  simpa [hx, h.left_not_mem] using h.not_connBetween

lemma isSepBetween_noEdge_of_ne (hne : x ≠ y) (hY : Y ⊆ X \ {x, y}) :
    (Graph.noEdge X β).IsSepBetween x y Y where
  subset := subset_diff.mp hY |>.1
  left_not_mem := (disjoint_iff_forall_notMem ..).mp (subset_diff.mp hY).2.symm (by simp)
  right_not_mem := (disjoint_iff_forall_notMem ..).mp (subset_diff.mp hY).2.symm (by simp)
  not_connBetween := by
    rintro ⟨W, hW, rfl, rfl⟩
    rw [isWalk_vertexDelete_iff] at hW
    exact hne hW.1.nil_of_noEdge.first_eq_last

@[simp]
lemma isEdgeSep_noEdge_iff : (Graph.noEdge X β).IsEdgeSep F ↔ F = ∅ ∧ X.encard ≠ 1 := by
  refine ⟨fun ⟨hF, h⟩ => ?_, ?_⟩
  · obtain rfl := by simpa using hF
    simpa [encard_eq_one] using h
  rintro ⟨rfl, hne⟩
  simpa [encard_eq_one] using hne

@[simp]
lemma isEdgeSep_bot_iff : (⊥ : Graph α β).IsEdgeSep F ↔ F = ∅ := by
  rw [← noEdge_empty, isEdgeSep_noEdge_iff]
  simp

@[simp]
lemma noEdge_connBetweenGE_iff (n : ℕ) : (Graph.noEdge X β).ConnBetweenGE x y n ↔
    n = 0 ∨ (x = y ∧ x ∈ X) := by
  refine ⟨fun h => ?_, ?_⟩
  · rw [or_iff_not_imp_right, not_and']
    rintro hne
    by_cases hxX : x ∈ X
    · simpa using h (isSepBetween_noEdge_of_ne (hne hxX) (by simp : ∅ ⊆ _))
    simpa [hxX] using h.left_mem
  rintro (rfl | ⟨rfl, hx⟩)
  · simp
  exact connBetweenGE_self hx n

@[simp]
lemma noEdge_preconnGE_iff (n : ℕ) : (Graph.noEdge X β).PreconnGE n ↔ n = 0 ∨ X.Subsingleton := by
  refine ⟨fun h => ?_, ?_⟩
  · rw [or_iff_not_imp_right, not_subsingleton_iff]
    rintro ⟨x, hx, y, hy, hne⟩
    simpa using h hx hy (isSepBetween_noEdge_of_ne hne (by simp : ∅ ⊆ _))
  rintro (rfl | hss) u v hu hv C hC
  · simp
  obtain rfl := hss hu hv
  exact (hC.ne_of_noEdge hu rfl).elim

@[simp]
lemma noEdge_ConnGE_iff (n : ℕ) : (Graph.noEdge X β).ConnGE n ↔ n = 0 ∨ (n = 1 ∧ ∃ x, X = {x}):= by
  obtain hc | hc := em ((Graph.noEdge X β).IsComplete) |>.symm
  · rw [← preconnGE_iff_connGE_of_not_isComplete hc, noEdge_preconnGE_iff]
    constructor
    · rintro (rfl | hss)
      · tauto
      simp [hss] at hc
    rintro (rfl | ⟨rfl, x, rfl⟩) <;> simp
  rw [hc.connGE_iff]
  rw [noEdge_isComplete_iff] at hc
  simp only [noEdge_vertexSet, hc, true_and]
  obtain (rfl | ⟨x, rfl⟩) := hc.eq_empty_or_singleton
  · simp
  simp only [encard_singleton, cast_le_one, cast_lt_one, singleton_eq_singleton_iff, exists_eq',
    and_true]
  omega

@[simp]
lemma ConnBetweenGE_bouquet_self (n : ℕ) : (bouquet v F).ConnBetweenGE v v n :=
  connBetweenGE_self (by simp) n

example : (bouquet v F).Preconnected := by simp only [bouquet_isComplete, IsComplete.preconnected]
example : (bouquet v F).Connected := by simp
example : (bouquet v F).IsSep S ↔ S = {v} := by simp
example (n : ℕ) : (bouquet v F).PreconnGE n := by simp
example (n : ℕ) : (bouquet v F).ConnGE n ↔ n ≤ 1 := by simp

example : (Graph.singleEdge u v e).Preconnected := by simp
example : (Graph.singleEdge u v e).Connected := by simp

lemma preconnected_iff_of_edgeSet_empty (hE : E(G) = ∅) : G.Preconnected ↔ V(G).Subsingleton := by
  refine ⟨fun h u hu v hv↦ ?_, fun h u v hu hv ↦ ?_⟩
  · obtain ⟨w, hw, rfl, rfl⟩ := h u v hu hv
    match w with
    | .nil u => simp
    | .cons u e w => simpa [hE] using hw.edge_mem_of_mem (e := e) (by simp)
  obtain rfl := h hu hv
  simpa

lemma connected_iff_of_edgeSet_empty (hE : E(G) = ∅) : G.Connected ↔ ∃ v, V(G) = {v} := by
  rw [connected_iff, preconnected_iff_of_edgeSet_empty hE,
    exists_eq_singleton_iff_nonempty_subsingleton]

@[simps (attr := grind =)]
def singleEdge_isEdgeSep (hne : u ≠ v) : (Graph.singleEdge u v e).IsEdgeSep {e} where
  subset_edgeSet := by simp
  not_connected h := by
    rw [connected_iff_of_edgeSet_empty (by simp),
      exists_eq_singleton_iff_nonempty_subsingleton] at h
    exact hne <| h.2 (by simp : u ∈ _) (by simp : v ∈ _)

example : (Graph.singleEdge u v e).IsSep S ↔ S = {u, v} := by simp
example (n : ℕ) : (Graph.singleEdge u v e).PreconnGE n := by simp

@[simp]
lemma singleEdge_connGE (hne : u ≠ v) (n : ℕ) : (Graph.singleEdge u v e).ConnGE n ↔ n ≤ 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ConnGE.anti_right h (by simp)⟩
  have := by simpa [hne, encard_pair] using h.le_card
  omega

@[simp]
lemma banana_preconnected_iff : (banana u v F).Preconnected ↔ u = v ∨ F.Nonempty := by
  refine ⟨fun h => ?_, ?_⟩
  · rw [or_iff_not_imp_right, not_nonempty_iff_eq_empty]
    rintro rfl
    simpa using h u v (by simp) (by simp)
  rintro (rfl | hF)
  · simp
  simp [hF]

@[simp]
lemma banana_connected_iff : (banana u v F).Connected ↔ u = v ∨ F.Nonempty := by
  rw [connected_iff]
  simp

@[simp]
lemma banana_preconnGE_iff : (banana u v F).PreconnGE n ↔ n = 0 ∨ u = v ∨ F.Nonempty := by
  refine ⟨fun hcon => ?_, fun h => ?_⟩
  · rw [or_iff_not_imp_right]
    simp only [← ne_eq, not_or, not_nonempty_iff_eq_empty]
    rintro ⟨hne, rfl⟩
    simpa [hne] using hcon
  rw [← banana_isComplete_iff] at h
  obtain rfl | hc := h
  · simp
  simp [hc]

@[simp]
lemma banana_connGE_iff : (banana u v F).ConnGE n ↔ n = 0 ∨ (n = 1 ∧ (u = v ∨ F.Nonempty)) := by
  obtain hc | hc := em ((banana u v F).IsComplete) |>.symm
  · simp [← banana_isComplete_iff, hc, ← preconnGE_iff_connGE_of_not_isComplete hc]
  simp only [hc.connGE_iff, banana_vertexSet, pair_subsingleton_iff, ← banana_isComplete_iff, hc,
    and_true]
  constructor
  · rintro (⟨rfl, hle⟩ | hlt)
    · simp only [mem_singleton_iff, insert_eq_of_mem, encard_singleton, cast_le_one] at hle
      omega
    have := encard_pair_le u v
    enat_to_nat!
    omega
  rintro (rfl | rfl)
  · simp
  obtain (rfl | hne) := eq_or_ne u v
  · simp
  simp [encard_pair hne]

private def k33LeftLeftPath (i i' j : Fin 3) : WList (ℕ ⊕ ℕ) (ℕ × ℕ) :=
  cons (Sum.inl (i : ℕ)) ((i : ℕ), (j : ℕ))
    (cons (Sum.inr (j : ℕ)) ((i' : ℕ), (j : ℕ)) (nil (Sum.inl (i' : ℕ))))

private def k33RightRightPath (j j' i : Fin 3) : WList (ℕ ⊕ ℕ) (ℕ × ℕ) :=
  cons (Sum.inr (j : ℕ)) ((i : ℕ), (j : ℕ))
    (cons (Sum.inl (i : ℕ)) ((i : ℕ), (j' : ℕ)) (nil (Sum.inr (j' : ℕ))))

private def k33LeftLeftEnsemble (i i' : Fin 3) (hii' : i ≠ i') :
    K33.VertexEnsemble (Sum.inl (i : ℕ)) (Sum.inl (i' : ℕ)) (Fin 3) where
  f := k33LeftLeftPath i i'
  isPath j := by
    have hii'_nat : (i : ℕ) ≠ (i' : ℕ) := fun h => hii' (Fin.ext h)
    simp [k33LeftLeftPath, CompleteBipartiteGraph, hii'_nat]
  first_eq j := by simp [k33LeftLeftPath]
  last_eq j := by simp [k33LeftLeftPath]
  internallyDisjoint j k hjk := by
    have hjk_nat : (j : ℕ) ≠ (k : ℕ) := fun h => hjk (Fin.ext h)
    ext x
    cases x with
    | inl a => simp [k33LeftLeftPath]
    | inr a =>
        simp [k33LeftLeftPath]
        intro h h'
        exact hjk_nat (h.symm.trans h')

private lemma k33LeftLeftEnsemble_edgeDisjoint (i i' : Fin 3) (hii' : i ≠ i') :
    (k33LeftLeftEnsemble i i' hii').edgeDisjoint := by
  intro j k hjk
  have hii'_nat : (i : ℕ) ≠ (i' : ℕ) := fun h => hii' (Fin.ext h)
  have hjk_nat : (j : ℕ) ≠ (k : ℕ) := fun h => hjk (Fin.ext h)
  show Disjoint E(k33LeftLeftPath i i' j) E(k33LeftLeftPath i i' k)
  rw [Set.disjoint_left]
  intro e hej hek
  simp [k33LeftLeftPath] at hej hek
  aesop

private def k33RightRightEnsemble (j j' : Fin 3) (hjj' : j ≠ j') :
    K33.VertexEnsemble (Sum.inr (j : ℕ)) (Sum.inr (j' : ℕ)) (Fin 3) where
  f := k33RightRightPath j j'
  isPath i := by
    have hjj'_nat : (j : ℕ) ≠ (j' : ℕ) := fun h => hjj' (Fin.ext h)
    simp [k33RightRightPath, CompleteBipartiteGraph, hjj'_nat]
  first_eq i := by simp [k33RightRightPath]
  last_eq i := by simp [k33RightRightPath]
  internallyDisjoint i k hik := by
    have hik_nat : (i : ℕ) ≠ (k : ℕ) := fun h => hik (Fin.ext h)
    ext x
    cases x with
    | inl a =>
        simp [k33RightRightPath]
        intro h h'
        exact hik_nat (h.symm.trans h')
    | inr a => simp [k33RightRightPath]

private lemma k33RightRightEnsemble_edgeDisjoint (j j' : Fin 3) (hjj' : j ≠ j') :
    (k33RightRightEnsemble j j' hjj').edgeDisjoint := by
  intro i k hik
  have hjj'_nat : (j : ℕ) ≠ (j' : ℕ) := fun h => hjj' (Fin.ext h)
  have hik_nat : (i : ℕ) ≠ (k : ℕ) := fun h => hik (Fin.ext h)
  show Disjoint E(k33RightRightPath j j' i) E(k33RightRightPath j j' k)
  rw [Set.disjoint_left]
  intro e hei hek
  simp [k33RightRightPath] at hei hek
  aesop

lemma k33_connBetweenGE_left_left (i i' : Fin 3) (hii' : i ≠ i') :
    K33.ConnBetweenGE (Sum.inl (i : ℕ)) (Sum.inl (i' : ℕ)) 3 := by
  rw [Menger'sTheorem_vertex (by simp) (by simp) (by simp : ENat.card (Fin 3) = 3)]
  exact ⟨k33LeftLeftEnsemble i i' hii'⟩

lemma k33_connBetweenGE_right_right (j j' : Fin 3) (hjj' : j ≠ j') :
    K33.ConnBetweenGE (Sum.inr (j : ℕ)) (Sum.inr (j' : ℕ)) 3 := by
  rw [Menger'sTheorem_vertex (by simp) (by simp) (by simp : ENat.card (Fin 3) = 3)]
  exact ⟨k33RightRightEnsemble j j' hjj'⟩

lemma k33_connBetweenGE_left_left' {i i' : ℕ} (hi : i < 3) (hi' : i' < 3) (hii' : i ≠ i') :
    K33.ConnBetweenGE (Sum.inl i) (Sum.inl i') 3 := by
  exact k33_connBetweenGE_left_left ⟨i, hi⟩ ⟨i', hi'⟩ (fun h ↦ hii' <| congrArg Fin.val h)

lemma k33_connBetweenGE_right_right' {j j' : ℕ} (hj : j < 3) (hj' : j' < 3) (hjj' : j ≠ j') :
    K33.ConnBetweenGE (Sum.inr j) (Sum.inr j') 3 := by
  exact k33_connBetweenGE_right_right ⟨j, hj⟩ ⟨j', hj'⟩ (fun h ↦ hjj' <| congrArg Fin.val h)

lemma k33_connBetweenGE_cross' {i j : ℕ} (hi : i < 3) (hj : j < 3) :
    K33.ConnBetweenGE (Sum.inl i) (Sum.inr j) 3 := by
  refine Adj.connBetweenGE ?_ 3
  rw [completeBipartiteGraph_adj_iff]
  exact Or.inl ⟨i, hi, j, hj, rfl, rfl⟩

lemma k33_preconnGE_three : K33.PreconnGE 3 := by
  intro s t hs ht
  cases s with
  | inl i =>
      have hi : i < 3 := by simpa [K33, CompleteBipartiteGraph] using hs
      cases t with
      | inl i' =>
          have hi' : i' < 3 := by simpa [K33, CompleteBipartiteGraph] using ht
          by_cases hii' : i = i'
          · subst hii'
            exact connBetweenGE_self hs 3
          · exact k33_connBetweenGE_left_left' hi hi' hii'
      | inr j =>
          have hj : j < 3 := by simpa [K33, CompleteBipartiteGraph] using ht
          exact k33_connBetweenGE_cross' hi hj
  | inr j =>
      have hj : j < 3 := by simpa [K33, CompleteBipartiteGraph] using hs
      cases t with
      | inl i =>
          have hi : i < 3 := by simpa [K33, CompleteBipartiteGraph] using ht
          simpa [adj_comm] using (k33_connBetweenGE_cross' hi hj).symm
      | inr j' =>
          have hj' : j' < 3 := by simpa [K33, CompleteBipartiteGraph] using ht
          by_cases hjj' : j = j'
          · subst hjj'
            exact connBetweenGE_self hs 3
          · exact k33_connBetweenGE_right_right' hj hj' hjj'

lemma k33_not_isComplete : ¬ K33.IsComplete := by
  intro h
  have h01 := h (Sum.inl 0) (by simp [K33, CompleteBipartiteGraph])
    (Sum.inl 1) (by simp [K33, CompleteBipartiteGraph]) (by simp)
  simp [completeBipartiteGraph_adj_iff] at h01

lemma k33_connGE_three : K33.ConnGE 3 := by
  rw [← preconnGE_iff_connGE_of_not_isComplete k33_not_isComplete 3]
  exact k33_preconnGE_three

lemma k33_connected : K33.Connected :=
  (connGE_one_iff.mp <| k33_connGE_three.anti_right (by omega))

lemma k33_edgeConnBetweenGE_left_left (i i' : Fin 3) (hii' : i ≠ i') :
    K33.EdgeConnBetweenGE (Sum.inl (i : ℕ)) (Sum.inl (i' : ℕ)) 3 :=
  edgeConnBetweenGE_of_edgeDisjoint (k33LeftLeftEnsemble i i' hii')
    (k33LeftLeftEnsemble_edgeDisjoint i i' hii') (by simp)

lemma k33_edgeConnBetweenGE_right_right (j j' : Fin 3) (hjj' : j ≠ j') :
    K33.EdgeConnBetweenGE (Sum.inr (j : ℕ)) (Sum.inr (j' : ℕ)) 3 :=
  edgeConnBetweenGE_of_edgeDisjoint (k33RightRightEnsemble j j' hjj')
    (k33RightRightEnsemble_edgeDisjoint j j' hjj') (by simp)

private def k33CrossDirectPath (i j : Fin 3) : WList (ℕ ⊕ ℕ) (ℕ × ℕ) :=
  cons (Sum.inl (i : ℕ)) ((i : ℕ), (j : ℕ)) (nil (Sum.inr (j : ℕ)))

private def k33CrossLongPath (i j : Fin 3) (k : Fin 2) : WList (ℕ ⊕ ℕ) (ℕ × ℕ) :=
  let i' : Fin 3 := i.succAbove k
  let j' : Fin 3 := j.succAbove k
  cons (Sum.inl (i : ℕ)) ((i : ℕ), (j' : ℕ))
    (cons (Sum.inr (j' : ℕ)) ((i' : ℕ), (j' : ℕ))
      (cons (Sum.inl (i' : ℕ)) ((i' : ℕ), (j : ℕ)) (nil (Sum.inr (j : ℕ)))))

@[simp] private lemma coe_succAbove_ne_self {n : ℕ} (p : Fin (n + 1)) (i : Fin n) :
    ↑(p.succAbove i) ≠ (p : ℕ) := fun h ↦ Fin.succAbove_ne p i <| Fin.ext h

@[simp] private lemma coe_self_ne_succAbove {n : ℕ} (p : Fin (n + 1)) (i : Fin n) :
    (p : ℕ) ≠ ↑(p.succAbove i) := fun h ↦ Fin.ne_succAbove p i <| Fin.ext h

@[simp] private lemma coe_succAbove_zero_ne_one (p : Fin 3) :
    ↑(p.succAbove 0) ≠ ↑(p.succAbove 1) := by
  intro h
  have : (0 : Fin 2) = 1 := Fin.succAbove_right_injective h
  omega

@[simp] private lemma coe_succAbove_one_ne_zero (p : Fin 3) :
    ↑(p.succAbove 1) ≠ ↑(p.succAbove 0) := by
  intro h
  exact coe_succAbove_zero_ne_one p h.symm

private def k33CrossPath (i j : Fin 3) : Option Bool → WList (ℕ ⊕ ℕ) (ℕ × ℕ)
  | none => k33CrossDirectPath i j
  | some false => k33CrossLongPath i j 0
  | some true => k33CrossLongPath i j 1

private lemma k33CrossPath_isPath (i j : Fin 3) : ∀ k, K33.IsPath (k33CrossPath i j k)
  | none => by simp [k33CrossPath, k33CrossDirectPath, CompleteBipartiteGraph]
  | some false => by
      simp [k33CrossPath, k33CrossLongPath, CompleteBipartiteGraph, coe_succAbove_ne_self,
        coe_self_ne_succAbove]
  | some true => by
      simp [k33CrossPath, k33CrossLongPath, CompleteBipartiteGraph, coe_succAbove_ne_self,
        coe_self_ne_succAbove]

private lemma k33CrossPath_first (i j : Fin 3) : ∀ k, (k33CrossPath i j k).first = Sum.inl (i : ℕ)
  | none => by simp [k33CrossPath, k33CrossDirectPath]
  | some false => by simp [k33CrossPath, k33CrossLongPath]
  | some true => by simp [k33CrossPath, k33CrossLongPath]

private lemma k33CrossPath_last (i j : Fin 3) : ∀ k, (k33CrossPath i j k).last = Sum.inr (j : ℕ)
  | none => by simp [k33CrossPath, k33CrossDirectPath]
  | some false => by simp [k33CrossPath, k33CrossLongPath]
  | some true => by simp [k33CrossPath, k33CrossLongPath]

private lemma k33CrossPath_edgeDisjoint (i j : Fin 3) :
    Pairwise (Disjoint on WList.edgeSet on k33CrossPath i j) := by
  intro k l hkl
  cases k with
  | none =>
      cases l with
      | none => contradiction
      | some b =>
          cases b
          · change Disjoint E(k33CrossPath i j none) E(k33CrossPath i j (some false))
            rw [Set.disjoint_left]
            have hji : (j : ℕ) ≠ ↑(j.succAbove 0) := coe_self_ne_succAbove j 0
            have hii : (i : ℕ) ≠ ↑(i.succAbove 0) := coe_self_ne_succAbove i 0
            intro e he1 he2
            simp [k33CrossPath, k33CrossDirectPath, k33CrossLongPath] at he1 he2
            aesop
          · change Disjoint E(k33CrossPath i j none) E(k33CrossPath i j (some true))
            rw [Set.disjoint_left]
            have hji : (j : ℕ) ≠ ↑(j.succAbove 1) := coe_self_ne_succAbove j 1
            have hii : (i : ℕ) ≠ ↑(i.succAbove 1) := coe_self_ne_succAbove i 1
            intro e he1 he2
            simp [k33CrossPath, k33CrossDirectPath, k33CrossLongPath] at he1 he2
            aesop
  | some b =>
      cases b with
      | false =>
          cases l with
          | none =>
              change Disjoint E(k33CrossPath i j (some false)) E(k33CrossPath i j none)
              rw [Set.disjoint_left]
              have hji : (j : ℕ) ≠ ↑(j.succAbove 0) := coe_self_ne_succAbove j 0
              have hii : (i : ℕ) ≠ ↑(i.succAbove 0) := coe_self_ne_succAbove i 0
              intro e he1 he2
              simp [k33CrossPath, k33CrossDirectPath, k33CrossLongPath] at he1 he2
              aesop
          | some b' =>
              cases b' with
              | false => contradiction
              | true =>
                  change Disjoint E(k33CrossPath i j (some false)) E(k33CrossPath i j (some true))
                  rw [Set.disjoint_left]
                  have hj01 : ↑(j.succAbove 0) ≠ ↑(j.succAbove 1) := coe_succAbove_zero_ne_one j
                  have hj10 : ↑(j.succAbove 1) ≠ ↑(j.succAbove 0) := coe_succAbove_one_ne_zero j
                  have hi01 : ↑(i.succAbove 0) ≠ ↑(i.succAbove 1) := coe_succAbove_zero_ne_one i
                  have hi10 : ↑(i.succAbove 1) ≠ ↑(i.succAbove 0) := coe_succAbove_one_ne_zero i
                  have hji : (j : ℕ) ≠ ↑(j.succAbove 0) := coe_self_ne_succAbove j 0
                  have hij : ↑(j.succAbove 1) ≠ (j : ℕ) := coe_succAbove_ne_self j 1
                  have hii : (i : ℕ) ≠ ↑(i.succAbove 0) := coe_self_ne_succAbove i 0
                  have hii' : ↑(i.succAbove 1) ≠ (i : ℕ) := coe_succAbove_ne_self i 1
                  have hcontra_i : ∀ {a : ℕ}, ↑(i.succAbove 1) = a → ↑(i.succAbove 0) = a → False :=
                    fun h1 h0 ↦ by
                      have hEq : i.succAbove 1 = i.succAbove 0 := Fin.ext (h1.trans h0.symm)
                      have : (1 : Fin 2) = 0 := Fin.succAbove_right_injective hEq
                      omega
                  have hcontra_j : ∀ {a : ℕ}, ↑(j.succAbove 1) = a → ↑(j.succAbove 0) = a → False :=
                    fun h1 h0 ↦ by
                      have hEq : j.succAbove 1 = j.succAbove 0 := Fin.ext (h1.trans h0.symm)
                      have : (1 : Fin 2) = 0 := Fin.succAbove_right_injective hEq
                      omega
                  intro e he1 he2
                  simp [k33CrossPath, k33CrossLongPath] at he1 he2
                  aesop
      | true =>
          cases l with
          | none =>
              change Disjoint E(k33CrossPath i j (some true)) E(k33CrossPath i j none)
              rw [Set.disjoint_left]
              have hji : (j : ℕ) ≠ ↑(j.succAbove 1) := coe_self_ne_succAbove j 1
              have hii : (i : ℕ) ≠ ↑(i.succAbove 1) := coe_self_ne_succAbove i 1
              intro e he1 he2
              simp [k33CrossPath, k33CrossDirectPath, k33CrossLongPath] at he1 he2
              aesop
          | some b' =>
              cases b' with
              | false =>
                  change Disjoint E(k33CrossPath i j (some true)) E(k33CrossPath i j (some false))
                  rw [Set.disjoint_left]
                  have hj01 : ↑(j.succAbove 0) ≠ ↑(j.succAbove 1) := coe_succAbove_zero_ne_one j
                  have hj10 : ↑(j.succAbove 1) ≠ ↑(j.succAbove 0) := coe_succAbove_one_ne_zero j
                  have hi01 : ↑(i.succAbove 0) ≠ ↑(i.succAbove 1) := coe_succAbove_zero_ne_one i
                  have hi10 : ↑(i.succAbove 1) ≠ ↑(i.succAbove 0) := coe_succAbove_one_ne_zero i
                  have hij : ↑(j.succAbove 0) ≠ (j : ℕ) := coe_succAbove_ne_self j 0
                  have hji : (j : ℕ) ≠ ↑(j.succAbove 1) := coe_self_ne_succAbove j 1
                  have hii' : ↑(i.succAbove 0) ≠ (i : ℕ) := coe_succAbove_ne_self i 0
                  have hii : (i : ℕ) ≠ ↑(i.succAbove 1) := coe_self_ne_succAbove i 1
                  have hcontra_i : ∀ {a : ℕ}, ↑(i.succAbove 0) = a → ↑(i.succAbove 1) = a → False :=
                    fun h0 h1 ↦ by
                      have hEq : i.succAbove 0 = i.succAbove 1 := Fin.ext (h0.trans h1.symm)
                      have : (0 : Fin 2) = 1 := Fin.succAbove_right_injective hEq
                      omega
                  have hcontra_j : ∀ {a : ℕ}, ↑(j.succAbove 0) = a → ↑(j.succAbove 1) = a → False :=
                    fun h0 h1 ↦ by
                      have hEq : j.succAbove 0 = j.succAbove 1 := Fin.ext (h0.trans h1.symm)
                      have : (0 : Fin 2) = 1 := Fin.succAbove_right_injective hEq
                      omega
                  intro e he1 he2
                  simp [k33CrossPath, k33CrossLongPath] at he1 he2
                  aesop
              | true => contradiction

lemma k33_edgeConnBetweenGE_cross (i j : Fin 3) :
    K33.EdgeConnBetweenGE (Sum.inl (i : ℕ)) (Sum.inr (j : ℕ)) 3 :=
  edgeConnBetweenGE_of_pathFamily (k33CrossPath i j) (k33CrossPath_isPath i j)
    (k33CrossPath_first i j) (k33CrossPath_last i j) (k33CrossPath_edgeDisjoint i j)
    (by simp)

lemma k33_edgeConnGE_three : K33.EdgeConnGE 3 := by
  intro s t hs ht
  cases s with
  | inl i =>
      have hi : i < 3 := by simpa [K33, CompleteBipartiteGraph] using hs
      cases t with
      | inl i' =>
          have hi' : i' < 3 := by simpa [K33, CompleteBipartiteGraph] using ht
          by_cases hii' : i = i'
          · subst hii'
            exact edgeConnBetweenGE_self hs 3
          · exact k33_edgeConnBetweenGE_left_left ⟨i, hi⟩ ⟨i', hi'⟩
              (fun h ↦ hii' <| congrArg Fin.val h)
      | inr j =>
          have hj : j < 3 := by simpa [K33, CompleteBipartiteGraph] using ht
          exact k33_edgeConnBetweenGE_cross ⟨i, hi⟩ ⟨j, hj⟩
  | inr j =>
      have hj : j < 3 := by simpa [K33, CompleteBipartiteGraph] using hs
      cases t with
      | inl i =>
          have hi : i < 3 := by simpa [K33, CompleteBipartiteGraph] using ht
          exact (k33_edgeConnBetweenGE_cross ⟨i, hi⟩ ⟨j, hj⟩).symm
      | inr j' =>
          have hj' : j' < 3 := by simpa [K33, CompleteBipartiteGraph] using ht
          by_cases hjj' : j = j'
          · subst hjj'
            exact edgeConnBetweenGE_self hs 3
          · exact k33_edgeConnBetweenGE_right_right ⟨j, hj⟩ ⟨j', hj'⟩
              (fun h ↦ hjj' <| congrArg Fin.val h)
