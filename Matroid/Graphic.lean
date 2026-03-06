import Matroid.Axioms.Circuit
import Matroid.Connectivity.Separation.Tutte
import Matroid.Minor.Contract
import Matroid.Graph.Forest
import Matroid.Graph.Connected.MixedLineGraph
import Matroid.Graph.Minor.Conn

variable {α β : Type*} {G H : Graph α β} {u v x x₁ x₂ y y₁ y₂ z : α} {e e' f g : β}
  {U V S T : Set α} {F F' R R': Set β} {C w P Q : WList α β}

open Set WList Matroid

namespace Graph

/-- The cycle matroid of a graph `G`. Its circuits are the edge sets of cycles of `G`,
and its independent sets are the edge sets of forests. -/
@[simps! E]
def cycleMatroid (G : Graph α β) : Matroid β :=
  FiniteCircuitMatroid.matroid <| FiniteCircuitMatroid.mk
    (E := E(G))
    (IsCircuit := G.IsCycleSet)
    (by
      simp only [IsCycleSet, not_exists, not_and]
      exact fun C hC hCe ↦ by simpa [hCe] using hC.nonempty.edgeSet_nonempty )
    (by
      rintro _ ⟨C₁, hC₁, rfl⟩ _ ⟨C₂, hC₂, rfl⟩ hne (hss : E(C₁) ⊆ E(C₂))
      have h_eq := hC₂.toGraph_eq_of_le hC₁ <|
        hC₁.isWalk.le_of_edgeSet_subset hC₁.nonempty hC₂.isWalk hss
      exact hne <| by simpa using congrArg Graph.edgeSet h_eq )
    (by
      rintro _ _ e ⟨C₁, hC₁, rfl⟩ ⟨C₂, hC₂, rfl⟩ hne he₁ he₂
      obtain ⟨x, y, hxy₁⟩ := C₁.exists_isLink_of_mem_edge he₁
      have hxy₂ := (hC₁.isWalk.isLink_iff_isLink_of_mem he₁).1 hxy₁
      rw [← hC₂.isWalk.isLink_iff_isLink_of_mem he₂] at hxy₂
      obtain ⟨P₁, hP₁, hP₁C₁, hx₁, hy₁⟩ := hC₁.exists_isPath_toGraph_eq_delete_edge_of_isLink hxy₁
      obtain ⟨P₂, hP₂, hP₂C₂, hx₂, hy₂⟩ := hC₂.exists_isPath_toGraph_eq_delete_edge_of_isLink hxy₂
      by_cases h_eq : P₁ = P₂
      · apply_fun (fun P : WList α β ↦ insert e E(P)) at h_eq
        simp [← P₁.toGraph_edgeSet, ← P₂.toGraph_edgeSet, hP₁C₁, hP₂C₂, edgeDelete_edgeSet,
          WList.toGraph_edgeSet, Set.insert_eq_of_mem he₁, Set.insert_eq_of_mem he₂, hne] at h_eq
      obtain ⟨C, hC, hCE⟩ := twoPaths hP₁ hP₂ h_eq (by rw [hx₁, hx₂]) (by rw [hy₁, hy₂])
      have hss : E(C) ⊆ (E(C₁) ∪ E(C₂)) \ {e} := by
        apply_fun Graph.edgeSet at hP₁C₁ hP₂C₂
        simp only [WList.toGraph_edgeSet, edgeDelete_edgeSet] at hP₁C₁ hP₂C₂
        rwa [union_diff_distrib, ← hP₁C₁, ← hP₂C₂]
      refine ⟨E(C), ⟨C, hC, rfl⟩, notMem_subset hss (by simp), fun x hx ↦ ?_⟩
      simpa using (hss.trans diff_subset) hx )
    (by
      rintro _ ⟨C, hC, rfl⟩
      exact C.edgeSet_finite )
    (by
      rintro _ ⟨C, hC, rfl⟩
      simpa using edgeSet_mono hC.isWalk.toGraph_le )

@[simp]
lemma cycleMatroid_isCircuit : G.cycleMatroid.IsCircuit = G.IsCycleSet := by
  simp [cycleMatroid]

@[simp]
lemma cycleMatroid_indep : G.cycleMatroid.Indep = G.IsAcyclicSet := by
  ext I
  simp only [cycleMatroid, FiniteCircuitMatroid.matroid_indep_iff, IsCycleSet, IsAcyclicSet]
  aesop

-- @[simp]
-- lemma cycleMatroid_isCocircuit : G.cycleMatroid.IsCocircuit = G.IsBond := by
--   ext F
--   rw?

@[simp]
lemma cycleMatroid_edgeRestrict (G : Graph α β) (F : Set β) :
    (G ↾ F).cycleMatroid = G.cycleMatroid ↾ (E(G) ∩ F) := by
  refine ext_isCircuit rfl fun I hI ↦ ?_
  obtain ⟨hI, hIF⟩ := by simpa using hI
  simp [restrict_isCircuit_iff, hI, hIF]

@[simp]
lemma cycleMatroid_edgeDelete (G : Graph α β) (F : Set β) :
    (G ＼ F).cycleMatroid = G.cycleMatroid ＼ F :=
  ext_isCircuit rfl fun I hI ↦ by simp

-- lemma cycleMatroid_contract {φ} (hφ : H.connPartition.IsRepFun φ) (hHG : H ≤ G) :
--     (G /[φ, E(H)]).cycleMatroid = G.cycleMatroid ／ E(H) := by
--   refine ext_indep rfl fun I hI ↦ ?_
--   simp only [cycleMatroid_E, contract_edgeSet, cycleMatroid_indep, isAcyclicSet_iff] at hI ⊢
--   refine ⟨fun ⟨_, h⟩ => ?_, fun h => ?_⟩
--   · rw [contract_edgeRestrict_comm] at h

@[simp]
lemma cycleMatroid_vertexDelete_isolatedSet (G : Graph α β) :
    (G - I(G)).cycleMatroid = G.cycleMatroid := by
  refine ext_isCircuit ?_ fun I hI ↦ ?_
  · rw [cycleMatroid_E, cycleMatroid_E, vertexDelete_edgeSet_diff, setincEdges_isolatedSet,
      diff_empty]
  rw [cycleMatroid_isCircuit, cycleMatroid_isCircuit]
  refine ⟨fun h ↦ h.of_isLink (fun e x y hxy ↦ ?_), fun h ↦ h.of_isLink (fun e x y hxy ↦ ?_)⟩
  · exact hxy.1
  simp [hxy, hxy.left_not_isolated, hxy.right_not_isolated]

lemma cycleMatroid_isRestriction_of_isLink (hl : ∀ ⦃e x y⦄, G.IsLink e x y → H.IsLink e x y) :
    G.cycleMatroid ≤r H.cycleMatroid := by
  have hsu : E(G) ⊆ E(H) := by
    intro e he
    obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet he
    exact (hl hxy).edge_mem
  use E(G), hsu, ext_isCircuit rfl fun I hI ↦ ?_
  rw [← inter_eq_right.mpr hsu, ← cycleMatroid_edgeRestrict]
  simp only [cycleMatroid_isCircuit]
  refine ⟨fun h ↦ h.of_isLink (fun e x y hxy ↦ (hl hxy).of_le_of_mem edgeRestrict_le ?_),
    fun h ↦ h.of_isLink (fun e x y hxy ↦ ?_)⟩
  · simp [hxy.edge_mem, (hl hxy).edge_mem]
  obtain ⟨-, he⟩ := by simpa using hxy.edge_mem
  obtain ⟨u, v, huv⟩ := G.exists_isLink_of_mem_edgeSet he
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hl huv |>.eq_and_eq_or_eq_and_eq (hxy.of_le edgeRestrict_le)
  · exact huv
  exact huv.symm

lemma cycleMatroid_isRestriction_of_le (h : G ≤ H) : G.cycleMatroid ≤r H.cycleMatroid :=
  cycleMatroid_isRestriction_of_isLink h.2

private lemma isolatedSet_vertexDelete_isolatedSet (G : Graph α β) :
    I(G - I(G)) = ∅ := by
  ext x
  constructor
  · intro hx
    have hxV : x ∈ V(G - I(G)) := (G - I(G)).isolatedSet_subset hx
    have hxG : x ∈ V(G) := by
      simpa [vertexDelete_vertexSet] using hxV.1
    have hxI : x ∉ I(G) := by
      simpa [vertexDelete_vertexSet] using hxV.2
    have hnx : ¬ G.Isolated x := by
      simpa [mem_isolatedSet_iff] using hxI
    obtain ⟨e, hex⟩ := (not_isolated_iff hxG).1 hnx
    have hex' : (G - I(G)).Inc e x := by
      rw [vertexDelete_inc_iff]
      refine ⟨hex, fun heI ↦ ?_⟩
      obtain ⟨y, hyI, hey⟩ := (mem_setIncEdges_iff G (I(G))).1 heI
      exact (show False from (mem_isolatedSet_iff G y).1 hyI |>.not_inc hey)
    exact hx.not_inc hex'
  simp

private lemma exists_isLink_of_mem_vertex_of_isolatedSet_eq_empty (hI : I(G) = ∅) (hx : x ∈ V(G)) :
    ∃ e y, G.IsLink e x y := by
  obtain hix | h := isolated_or_exists_isLink hx
  · have : x ∈ I(G) := by simpa [mem_isolatedSet_iff] using hix
    simp [hI] at this
  exact h

private lemma exists_isCyclicWalk_of_cycleMatroid_connected [G.Loopless]
    (hconn : G.cycleMatroid.Connected) (he : e ∈ E(G)) (hf : f ∈ E(G)) (hef : e ≠ f) :
    ∃ C, G.IsCyclicWalk C ∧ e ∈ E(C) ∧ f ∈ E(C) := by
  obtain ⟨C, hC, heC, hfC⟩ := hconn.exists_isCircuit_of_ne
    (by simpa using he) (by simpa using hf) hef
  rw [cycleMatroid_isCircuit] at hC
  obtain ⟨C, hC', rfl⟩ := hC
  exact ⟨C, hC', by simpa using heC, by simpa using hfC⟩

private lemma cycleMatroid_connectedTo_of_incident [G.Loopless] (hconn : G.PreconnGE 2)
    (hxy : G.IsLink e x y) (hxz : G.IsLink f x z) :
    G.cycleMatroid.ConnectedTo e f := by
  by_cases hef : e = f
  · subst hef
    exact Matroid.connectedTo_self <| by simpa using hxy.edge_mem
  rw [Graph.preconnGE_iff_forall_preconnected] at hconn
  have hpre : (G - ({x} : Set α)).Preconnected := hconn (X := {x}) (by simp)
  obtain ⟨P, hP, rfl, rfl⟩ := (hpre y z
    ⟨hxy.right_mem, by simp [hxy.adj.ne.symm]⟩
    ⟨hxz.right_mem, by simp [hxz.adj.ne.symm]⟩).exists_isPath
  have hPx : x ∉ P := by
    intro hxP
    have hxV : x ∈ V(G - ({x} : Set α)) := hP.isWalk.vertex_mem_of_mem hxP
    simp [vertexDelete_vertexSet] at hxV
  have hP' : G.IsPath P := hP.of_le vertexDelete_le
  have hQ : G.IsPath (P.concat f x) := by
    rw [concat_isPath_iff]
    exact ⟨hP', hxz.symm, hPx⟩
  have heP : e ∉ P.edge := by
    intro heP
    have heP' : e ∈ E(P) := by simpa using heP
    have hdel : e ∉ E(G - ({x} : Set α)) := by
      intro hedel
      obtain ⟨a, b, hab⟩ := exists_isLink_of_mem_edgeSet hedel
      obtain ⟨habG, hax, hbx⟩ := (vertexDelete_isLink_iff G ({x} : Set α)).1 hab
      obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := habG.eq_and_eq_or_eq_and_eq hxy
      · exact hax rfl
      · exact hbx rfl
    exact hdel <| hP.isWalk.edgeSet_subset heP'
  have heQ : e ∉ (P.concat f x).edge := by
    simp [WList.concat_edge, heP, hef]
  let C : WList α β := cons x e (P.concat f x)
  have hC : G.IsCyclicWalk C := by
    dsimp [C]
    simpa using hQ.cons_isCyclicWalk (e := e) (by simpa using hxy.symm) heQ
  have hC' : G.cycleMatroid.IsCircuit E(C) := by
    rw [cycleMatroid_isCircuit]
    exact ⟨C, hC, rfl⟩
  exact hC'.mem_connectedTo_mem (by simp [C]) (by simp [C])

private lemma cycleMatroid_connectedTo_firstEdge_lastEdge_of_isWalk [G.Loopless]
    (hconn : G.PreconnGE 2) {W : WList α β} (hW : G.IsWalk W) (hne : W.Nonempty) :
    G.cycleMatroid.ConnectedTo hne.firstEdge hne.lastEdge := by
  obtain ⟨u, e, w, rfl⟩ := hne.exists_cons
  obtain ⟨v, rfl⟩ | hw := w.exists_eq_nil_or_nonempty
  · exact Matroid.connectedTo_self <| by simpa using (cons_isWalk_iff.mp hW).1.edge_mem
  obtain ⟨v, f, w', rfl⟩ := hw.exists_cons
  have h₁ : G.IsLink e u v := (cons_isWalk_iff.mp hW).1
  have htail : G.IsWalk (cons v f w') := (cons_isWalk_iff.mp hW).2
  have h₂ : G.IsLink f v w'.first := (cons_isWalk_iff.mp htail).1
  have htailConn : G.cycleMatroid.ConnectedTo f hne.lastEdge := by
    simpa [WList.Nonempty.firstEdge_cons, hne.lastEdge_cons] using
      cycleMatroid_connectedTo_firstEdge_lastEdge_of_isWalk hconn htail hw
  exact (cycleMatroid_connectedTo_of_incident hconn h₁.symm h₂).trans htailConn

private lemma cycleMatroid_connected_of_preconnGE_two [G.Loopless] (hconn : G.PreconnGE 2)
    (hE : E(G).Nonempty) : G.cycleMatroid.Connected := by
  refine ⟨?_, fun e f he hf ↦ ?_⟩
  · exact ⟨hE.choose, by simpa using hE.choose_spec⟩
  have hpre : G.Preconnected := by
    rw [← Graph.preconnGE_one_iff]
    exact hconn.anti_right (by decide : 1 ≤ 2)
  obtain ⟨W, hWne, hW, hfirst, hlast⟩ := Graph.Preconnected.exists_isWalk_firstEdge_lastEdge hpre
    (by simpa using he) (by simpa using hf)
  simpa [hfirst, hlast] using cycleMatroid_connectedTo_firstEdge_lastEdge_of_isWalk hconn hW hWne

private lemma cycleMatroid_tutteConnected_two_of_preconnGE_two [G.Loopless]
    (hconn : G.PreconnGE 2) : G.cycleMatroid.TutteConnected 2 := by
  by_cases hE : E(G).Nonempty
  · exact (cycleMatroid_connected_of_preconnGE_two hconn hE).tutteConnected_two
  refine Matroid.tutteConnected_of_subsingleton ?_ 2
  simp [cycleMatroid_E, Set.not_nonempty_iff_eq_empty.mp hE]

private lemma preconnGE_two_of_cycleMatroid_tutteConnected_two [G.Loopless]
    (hI : I(G) = ∅) (hconn : G.cycleMatroid.TutteConnected 2) :
    G.PreconnGE 2 := by
  rw [Graph.preconnGE_iff_forall_preconnected]
  intro X hX
  have hXss : X.Subsingleton := by
    refine encard_le_one_iff_subsingleton.1 ?_
    enat_to_nat!
    omega
  obtain rfl | ⟨x, rfl⟩ := hXss.eq_empty_or_singleton
  · intro y z hy hz
    have hyG : y ∈ V(G) := by simpa [vertexDelete_vertexSet] using hy
    have hzG : z ∈ V(G) := by simpa [vertexDelete_vertexSet] using hz
    obtain ⟨e, u, heu⟩ := exists_isLink_of_mem_vertex_of_isolatedSet_eq_empty hI hyG
    obtain ⟨f, v, hfv⟩ := exists_isLink_of_mem_vertex_of_isolatedSet_eq_empty hI hzG
    by_cases hef : e = f
    · obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := heu.eq_and_eq_or_eq_and_eq (hef ▸ hfv)
      · exact ConnBetween.refl hy
      simpa [vertexDelete_empty] using heu.connBetween
    haveI : G.cycleMatroid.Nonempty := ⟨e, by simpa using heu.edge_mem⟩
    have hMconn : G.cycleMatroid.Connected := Matroid.tutteConnected_two_iff.mp hconn
    obtain ⟨C, hC, heC, hfC⟩ :=
      exists_isCyclicWalk_of_cycleMatroid_connected hMconn heu.edge_mem hfv.edge_mem hef
    obtain ⟨y', u', hyu⟩ := C.exists_isLink_of_mem_edge heC
    obtain ⟨z', v', hzv⟩ := C.exists_isLink_of_mem_edge hfC
    have hyu' : G.IsLink e y' u' := (hC.isWalk.isLink_iff_isLink_of_mem heC).1 hyu
    have hzv' : G.IsLink f z' v' := (hC.isWalk.isLink_iff_isLink_of_mem hfC).1 hzv
    have hyC : y ∈ C := by
      obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hyu'.eq_and_eq_or_eq_and_eq heu
      · simpa using hyu.left_mem
      · simpa using hyu.right_mem
    have hzC : z ∈ C := by
      obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hzv'.eq_and_eq_or_eq_and_eq hfv
      · simpa using hzv.left_mem
      · simpa using hzv.right_mem
    simpa [vertexDelete_empty] using IsWalk.connBetween_of_mem_of_mem hC.isWalk hyC hzC
  · intro y z hy hz
    have hy' : y ∈ V(G) ∧ y ∉ ({x} : Set α) := by simpa [vertexDelete_vertexSet] using hy
    have hz' : z ∈ V(G) ∧ z ∉ ({x} : Set α) := by simpa [vertexDelete_vertexSet] using hz
    have hyG : y ∈ V(G) := hy'.1
    have hzG : z ∈ V(G) := hz'.1
    have hyx : y ≠ x := by simpa using hy'.2
    have hzx : z ≠ x := by simpa using hz'.2
    obtain ⟨e, u, heu⟩ := exists_isLink_of_mem_vertex_of_isolatedSet_eq_empty hI hyG
    obtain ⟨f, v, hfv⟩ := exists_isLink_of_mem_vertex_of_isolatedSet_eq_empty hI hzG
    by_cases hef : e = f
    · obtain hEq | hEq := heu.eq_and_eq_or_eq_and_eq (hef ▸ hfv)
      · rcases hEq with ⟨rfl, rfl⟩
        exact ConnBetween.refl hy
      rcases hEq with ⟨hyv, huz⟩
      subst u
      have hxy : (G - ({x} : Set α)).IsLink e y z := by
        rw [vertexDelete_isLink_iff]
        exact ⟨heu, hyx, hzx⟩
      exact hxy.connBetween
    haveI : G.cycleMatroid.Nonempty := ⟨e, by simpa using heu.edge_mem⟩
    have hMconn : G.cycleMatroid.Connected := Matroid.tutteConnected_two_iff.mp hconn
    obtain ⟨C, hC, heC, hfC⟩ :=
      exists_isCyclicWalk_of_cycleMatroid_connected hMconn heu.edge_mem hfv.edge_mem hef
    obtain ⟨y', u', hyu⟩ := C.exists_isLink_of_mem_edge heC
    obtain ⟨z', v', hzv⟩ := C.exists_isLink_of_mem_edge hfC
    have hyu' : G.IsLink e y' u' := (hC.isWalk.isLink_iff_isLink_of_mem heC).1 hyu
    have hzv' : G.IsLink f z' v' := (hC.isWalk.isLink_iff_isLink_of_mem hfC).1 hzv
    have hyC : y ∈ C := by
      obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hyu'.eq_and_eq_or_eq_and_eq heu
      · simpa using hyu.left_mem
      · simpa using hyu.right_mem
    have hzC : z ∈ C := by
      obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hzv'.eq_and_eq_or_eq_and_eq hfv
      · simpa using hzv.left_mem
      · simpa using hzv.right_mem
    exact hC.connBetween_deleteVertex_of_mem_of_mem x hyC hzC hyx hzx

theorem cycleMatroid_tutteConnected_two_iff_preconnGE_two [G.Loopless] :
    G.cycleMatroid.TutteConnected 2 ↔ (G - I(G)).PreconnGE 2 := by
  let G' := G - I(G)
  have hI : I(G') = ∅ := isolatedSet_vertexDelete_isolatedSet G
  have hEq : G'.cycleMatroid = G.cycleMatroid := cycleMatroid_vertexDelete_isolatedSet G
  constructor
  · intro h
    have h' : G'.cycleMatroid.TutteConnected 2 := by simpa [G', hEq] using h
    exact preconnGE_two_of_cycleMatroid_tutteConnected_two hI h'
  · intro h
    have h' : G'.cycleMatroid.TutteConnected 2 := cycleMatroid_tutteConnected_two_of_preconnGE_two h
    simpa [G', hEq] using h'

private lemma isolatedSet_eq_empty_of_connected_nontrivial
    (hG : G.Connected) (hV : V(G).Nontrivial) : I(G) = ∅ := by
  ext x
  constructor
  · intro hx
    have hxV : x ∈ V(G) := G.isolatedSet_subset hx
    obtain ⟨e, y, hxy, -⟩ := hG.exists_isLink_of_mem hV hxV
    exact False.elim <| (mem_isolatedSet_iff G x).1 hx |>.not_isLink hxy
  simp

theorem cycleMatroid_tutteConnected_two_iff_preconnGE_two_of_connected [G.Loopless]
    (hG : G.Connected) : G.cycleMatroid.TutteConnected 2 ↔ G.PreconnGE 2 := by
  obtain hss | hV := V(G).subsingleton_or_nontrivial
  · have hpre : G.PreconnGE 2 := by
      refine Graph.IsComplete.preconnGE ?_ 2
      intro x hx y hy hxy
      exact False.elim <| hxy <| hss hx hy
    have hE : E(G) = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro e he
      obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet he
      simp [hss hxy.left_mem hxy.right_mem] at hxy
    have hM : G.cycleMatroid.TutteConnected 2 := by
      refine Matroid.tutteConnected_of_subsingleton ?_ 2
      simp [cycleMatroid_E, hE]
    exact ⟨fun _ ↦ hpre, fun _ ↦ hM⟩
  have hI : I(G) = ∅ := isolatedSet_eq_empty_of_connected_nontrivial hG hV
  simpa [hI, vertexDelete_empty] using (cycleMatroid_tutteConnected_two_iff_preconnGE_two (G := G))
