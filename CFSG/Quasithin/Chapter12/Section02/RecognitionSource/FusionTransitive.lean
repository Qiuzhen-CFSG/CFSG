module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.GlobalTI
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.CentralQuotientFive
public import Theory.Representation.BinaryFourOrbit

/-!
# The rank-four alternating-seven branch of 12.2.16

The action on the original chosen Irr⁺ space has kernel exactly C_L(V).
Consequently its image has the order of the literal quotient L/C_L(V).
In row (e) this is A₇, whose order is divisible by 45. The binary four-space
orbit theorem makes the action transitive on all fifteen nonzero vectors.
The original inclusion of the chosen space into V then supplies conjugators
in L, and local TI with NoEscape gives global TI.

No action or transitivity on V/C_V(L) is substituted for the action on V.
Source: Aschbacher--Smith, 12.2.2(3e) and 12.2.16, printed pp.795,799--800.
-/

public noncomputable section

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
/-- Transport actual chosen-space transitivity to conjugation on the original V. -/
theorem chosen_vector_transitive (D : ChosenModule T L V)
    (ht : ∀ v w : D.space, v ≠ 0 → w ≠ 0 → ∃ l : L, D.chosenAction l v = w)
    {x y : G} (hx : x ∈ V) (hy : y ∈ V) (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    ∃ l ∈ L, l * x * l⁻¹ = y := by
  let v := (D.spaceEquiv.symm ⟨x,hx⟩).toAdd
  let w := (D.spaceEquiv.symm ⟨y,hy⟩).toAdd
  have hvalv : (v.val.toMul.val : G) = x :=
    (D.spaceEquiv_apply v).symm.trans
      (congrArg Subtype.val (D.spaceEquiv.apply_symm_apply ⟨x,hx⟩))
  have hvalw : (w.val.toMul.val : G) = y :=
    (D.spaceEquiv_apply w).symm.trans
      (congrArg Subtype.val (D.spaceEquiv.apply_symm_apply ⟨y,hy⟩))
  have hv : v ≠ 0 := by
    intro he
    exact hx1 (hvalv.symm.trans (congrArg (fun z : D.space => (z.val.toMul.val : G)) he))
  have hw : w ≠ 0 := by
    intro he
    exact hy1 (hvalw.symm.trans (congrArg (fun z : D.space => (z.val.toMul.val : G)) he))
  obtain ⟨l,hl⟩ := ht v w hv hw
  refine ⟨l,l.property,?_⟩
  have he := congrArg (fun z : D.space => (z.val.toMul.val : G)) hl
  change (l : G) * (v.val.toMul.val : G) * (l : G)⁻¹ = (w.val.toMul.val : G) at he
  rwa [hvalv,hvalw] at he

/-- Transitivity on the full chosen space discharges the global fusion step. -/
theorem globalTI_of_chosenAction_transitive
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222 K) (hnone : NoEscape L V)
    (ht : ∀ v w : D.space, v ≠ 0 → w ≠ 0 → ∃ l : L, D.chosenAction l v = w) :
    IsTISubgroup V := by
  apply globalTI_of_fusion h D structural hnone
  intro x y hx hy hx1 hy1 _
  obtain ⟨l,hl,he⟩ := chosen_vector_transitive D ht hx hy hx1 hy1
  exact ⟨l,L.le_normalizer hl,he⟩

/-- A four-dimensional action image divisible by 45 is already enough for TI. -/
theorem globalTI_of_four_dimensional_image
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222 K) (hnone : NoEscape L V)
    (hd : Module.finrank (ZMod 2) D.space = 4)
    (hc : 45 ∣ Nat.card (actionImage D.chosenAction)) : IsTISubgroup V := by
  apply globalTI_of_chosenAction_transitive h D structural hnone
  intro v w hv hw
  exact BinaryFourOrbit.representation_transitive D.chosenAction hd hc hv hw

omit [Finite G] in
private theorem chosen_action_group_ker (D : ChosenModule T L V) :
    D.chosenAction.asGroupHom.ker = (centralizer (V : Set G)).subgroupOf L := by
  ext l
  constructor
  · intro hl
    have hl' : D.chosenAction l = 1 := congrArg Units.val hl
    apply mem_centralizer_iff.mpr
    intro v hv
    obtain ⟨w,hw⟩ := D.spaceEquiv.surjective ⟨v,hv⟩
    have he := congrArg (fun z : D.space => (z.val.toMul.val : G))
      (LinearMap.congr_fun hl' w.toAdd)
    have hw' : (w.toAdd.val.toMul.val : G) = v :=
      (D.spaceEquiv_apply w.toAdd).symm.trans (congrArg Subtype.val hw)
    change (l : G) * (w.toAdd.val.toMul.val : G) * (l : G)⁻¹ =
      (w.toAdd.val.toMul.val : G) at he
    rw [hw'] at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro hl
    apply Units.ext
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    change (l : G) * (v.val.toMul.val : G) * (l : G)⁻¹ = (v.val.toMul.val : G)
    have hv : (v.val.toMul.val : G) ∈ V :=
      D.image_eq.le (mem_map_of_mem _ (mem_map_of_mem _ v.property))
    exact mul_inv_eq_iff_eq_mul.mpr ((mem_centralizer_iff.mp hl) _ hv).symm

/-- Complete source row (e), using its literal relative-centralizer quotient. -/
theorem globalTI_of_alternating_seven_four
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222 K) (hnone : NoEscape L V)
    [((centralizer (V : Set G)).subgroupOf L).Normal]
    (e : (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) D.space = 4) : IsTISubgroup V := by
  apply globalTI_of_four_dimensional_image h D structural hnone hd
  have hc : Nat.card (actionImage D.chosenAction) =
      Nat.card (L ⧸ (centralizer (V : Set G)).subgroupOf L) := by
    rw [actionImage, ← Nat.card_congr
      (QuotientGroup.quotientKerEquivRange D.chosenAction.asGroupHom).toEquiv]
    rw [chosen_action_group_ker D]
  rw [hc, Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
  norm_num [Nat.factorial]
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
