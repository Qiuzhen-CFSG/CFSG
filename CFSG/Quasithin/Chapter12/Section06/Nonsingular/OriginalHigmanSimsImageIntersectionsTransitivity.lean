module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsImageIntersectionsPure
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrderBound.Base

/-!
# Point transitivity in the marked HS sixteen-subgroup

Two explicit words in the original HS generators normalize the marked
sixteen-subgroup and act transitively on its fifteen nonidentity elements.
The permutation words, normalization tables, and fifteen transport words
are checked by the kernel on the original degree-100 carrier.
Source: the HS inspection in Aschbacher--Smith12.6.12, printed pp.825--826.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06.OriginalHigmanSimsImageIntersectionsNative
open Sporadic.LeechRelated.HS EvenLocalCandidates EvenLocalCandidates.SylowCatalogueData
set_option maxRecDepth 10000

private def letter : Fin 4 → Equiv.Perm (Fin 100) :=
  ![OrderCertificate.p0,OrderCertificate.p0⁻¹,OrderCertificate.p1,OrderCertificate.p1⁻¹]

private theorem letter_mem (i : Fin 4) : letter i ∈ generated := by
  have ha : OrderCertificate.p0 ∈ generated := by
    rw [OrderCertificate.a_eq_generator]
    exact subset_closure (by simp)
  have hb : OrderCertificate.p1 ∈ generated := by
    rw [OrderCertificate.b_eq_generator]
    exact subset_closure (by simp)
  fin_cases i
  · exact ha
  · exact generated.inv_mem ha
  · exact hb
  · exact generated.inv_mem hb

private theorem word_mem (w : List (Fin 4)) : evalWord letter w ∈ generated := by
  induction w with
  | nil => exact generated.one_mem
  | cons i w ih => exact generated.mul_mem (letter_mem i) ih

private def normalizerWord : Fin 2 → List (Fin 4) := ![[3, 0, 2, 2, 2, 0, 2, 2, 0, 3, 3, 0, 2, 2, 0, 2, 2, 0, 3, 0, 2, 0, 2, 0, 2, 0, 2, 2, 0, 3, 3, 0, 2, 2, 0, 2, 1, 2, 1, 2, 1, 3, 3, 1, 2, 2, 0, 2, 0, 2, 0, 3, 3, 0, 2, 0, 2, 2, 2, 0, 3, 3, 0, 0, 2, 2, 0, 3, 3, 0, 2, 2, 0, 2, 0, 2, 2, 0, 3, 3, 0, 3, 3],[2, 0, 3, 0, 2, 0, 3, 3, 3, 0, 2, 2, 0, 3, 0, 3, 0, 3, 3, 0, 2, 2, 0, 3, 3, 0, 3, 3, 0, 3, 0, 2, 2, 1, 3, 1, 3, 1, 2, 2, 0, 3, 3, 0, 2, 0, 2, 0, 3, 3, 0, 2]]

private def normalizerMap (i : Fin 2) (p : Fin 100) : Fin 100 :=
  ⟨(5244347789385369442807201400868836490247960443682999533164124655054350793290198412453964084374494227833121956092120880905617261057138428907311118327738913345435314030322684911917701219166156726951637900925363765027685470655699721741537265208304402921452756171226378758173363479066899020891788237795088158457638907207891583057669518955733249021860749232320436291397286317217437511022929389399452429661862466878710320827776 >>> (7*(100*i.val+p.val))) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private def normalizerInvMap (i : Fin 2) (p : Fin 100) : Fin 100 :=
  ⟨(17363021443659492327840923745647839484286852631996971791337530491767378395931192737140410446827336588446681385860275134013204982958149254799990485031372852121591875142576152456448793091367250243946227424497072961014008560904133297726773364963944468799194747685661782936763582995775232920400137805817060509900890698938026009261771587446379205801946053201125886882590709910850054618917426238370881752622491481422864799411072 >>> (7*(100*i.val+p.val))) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private theorem normalizer_inverse : ∀ (i : Fin 2) (p : Fin 100),
    normalizerInvMap i (normalizerMap i p) = p := by
  apply allFin₂
  decide +kernel

private def normalizerPerm (i : Fin 2) : Equiv.Perm (Fin 100) :=
  tablePerm (normalizerMap i) (normalizerInvMap i) (normalizer_inverse i)
    (rightInverse_of_leftInverse_fin (normalizer_inverse i))

private theorem normalizer_word : ∀ (i : Fin 2) (p : Fin 100),
    normalizerPerm i p = evalWord letter (normalizerWord i) p := by
  apply allFin₂
  decide +kernel

private def normalizerElement (i : Fin 2) : Carrier :=
  ⟨normalizerPerm i,by
    have he : normalizerPerm i = evalWord letter (normalizerWord i) :=
      Equiv.ext (normalizer_word i)
    rw [he]
    exact word_mem _⟩

private def actionRow : Fin 2 → Fin 16 → Fin 16 := ![![0,1,2,11,4,13,8,9,15,12,3,10,7,14,5,6],![0,14,6,15,8,4,13,5,3,11,1,2,9,12,10,7]]

private theorem action_point : ∀ (j : Fin 2) (i : Fin 16) (p : Fin 100),
    normalizerMap j (point (candidateRow 0 i) (normalizerInvMap j p)) =
      point (candidateRow 0 (actionRow j i)) p := by
  apply allFin
  decide +kernel

private theorem normalizer_action (j : Fin 2) (i : Fin 16) :
    (MulAut.conj (normalizerElement j)) (element (candidateRow 0 i)) =
      element (candidateRow 0 (actionRow j i)) := by
  apply Subtype.ext
  apply Equiv.ext
  intro p
  simp only [MulAut.conj_apply,Subgroup.coe_mul,Subgroup.coe_inv,
    Equiv.Perm.mul_apply,element_point]
  exact action_point j i p

private theorem normalizerElement_mem (j : Fin 2) :
    normalizerElement j ∈ normalizer (markedW : Set Carrier) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · rintro _ ⟨_,⟨i,rfl⟩,rfl⟩
    exact ⟨actionRow j i,(normalizer_action j i).symm⟩
  · rw [card_map_of_injective (MulAut.conj (normalizerElement j)).injective]

private def move : List (Fin 2) → Fin 16 → Fin 16
  | [],i => i
  | j::w,i => actionRow j (move w i)

private theorem eval_normalizes (w : List (Fin 2)) :
    evalWord normalizerElement w ∈ normalizer (markedW : Set Carrier) := by
  induction w with
  | nil => exact one_mem _
  | cons j w ih => exact mul_mem (normalizerElement_mem j) ih

private theorem eval_move (w : List (Fin 2)) (i : Fin 16) :
    (MulAut.conj (evalWord normalizerElement w)) (element (candidateRow 0 i)) =
      element (candidateRow 0 (move w i)) := by
  induction w with
  | nil => simp [evalWord,move]
  | cons j w ih =>
    change (MulAut.conj (normalizerElement j * evalWord normalizerElement w)) _ = _
    rw [map_mul]
    change (MulAut.conj (normalizerElement j))
      ((MulAut.conj (evalWord normalizerElement w)) _) = _
    rw [ih,normalizer_action]
    rfl

private def transportWord : Fin 16 → List (Fin 2) := ![[],[1, 0, 0, 1, 1],[],[1, 0],[1, 0, 1, 1],[1, 1, 1, 1, 0],[1, 0, 1, 0],[1, 1, 0],[1, 0, 1],[1, 1],[1, 0, 0],[1],[1, 1, 1],[1, 1, 1, 1],[1, 0, 0, 1],[1, 1, 0, 1]]

private theorem transport_spec : ∀ i : Fin 16, i ≠ 0 → move (transportWord i) i = 2 := by
  decide +kernel

private theorem point_eq : element (candidateRow 0 2) = e0 := by
  apply Subtype.ext
  apply Equiv.ext
  intro p
  rw [element_point]
  have h : ∀ p : Fin 100, point (candidateRow 0 2) p = (e0 : Equiv.Perm (Fin 100)) p := by
    apply allFin
    decide +kernel
  exact h p

/-- The chosen involution is an actual member of the marked subgroup. -/
theorem marked_point_mem : e0 ∈ markedW := ⟨2,point_eq⟩

/-- The chosen involution is nonidentity in the original carrier. -/
theorem marked_point_ne_one : e0 ≠ 1 := by
  intro he
  have hh := congrArg (fun x : Carrier => (x : Equiv.Perm (Fin 100)) 1) he
  have hn : (e0 : Equiv.Perm (Fin 100)) 1 ≠ 1 := by decide +kernel
  exact hn hh

/-- The actual HS normalizer is transitive on the nonidentity elements of
its marked elementary sixteen-subgroup. -/
theorem markedW_point_transitive (x : Carrier) (hx : x ∈ markedW) (hne : x ≠ 1) :
    ∃ g : Carrier, g ∈ normalizer (markedW : Set Carrier) ∧ (MulAut.conj g) x = e0 := by
  obtain ⟨i,rfl⟩ := hx
  have hi : i ≠ 0 := by
    intro he
    subst i
    exact hne (by rfl)
  refine ⟨evalWord normalizerElement (transportWord i),eval_normalizes _,?_⟩
  rw [eval_move,transport_spec i hi,point_eq]

end CFSG.Quasithin.Chapter12.Section06.OriginalHigmanSimsImageIntersectionsNative
