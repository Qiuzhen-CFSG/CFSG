module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SmallRows.SingleA5WholeAction
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.CenterAbovePoint.FivePoint

/-!
# The actual extraspecial closure of the normalized degree-four A₅

The proved whole five-point action of the original normalized component
satisfies the center-point criterion. Thus the actual closure U is
extraspecial of order 32, and the literal terminal-action kernel is
O₂(H). All action, movement and cohomology premises are discharged from
the original source prefix, for the same K and T-conjugate span.

These are local inputs to the remaining ambient field-four recognition
and Borel contradiction, owned by terminal solvability. In particular,
identifying the action kernel does not assert U=O₂(H).

Source: Aschbacher–Smith 14.3.6, 14.3.14–15 and 14.2.16–17,
printed pp.991,993–994,986–987.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
section Source
variable {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)

variable (hnot : ¬ ClassificationModels.IsTheoremEModel G) (g : G)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    {K : Subgroup G} (hK : ComponentLift F g K)
include hnot hgP hgH hyp hK


include hG hempty hM hu hmany hcard e hne

/-- The actual center of the degree-four normalized A₅ closure is the
original point, with no cohomology or movement premise. -/
theorem source_single_a5_center_eq_point_of_four
    (e5 : F.terminalDot K ≃* alternatingGroup (Fin 5))
    (hspan : K = conjugateSpanBy K (T : Subgroup G))
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4) : F.ZU = F.Vi 1 := by
  obtain ⟨c,p,hp,he,hc⟩ := source_single_a5_whole_action_of_four
    hG T hempty hM hu hmany hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  let d := Recognition.rankTwo_closure_geometry h F hne
  have hnK : (K.subgroupOf F.H).Normal := by
    have hh := hK.normal_span
    rwa [←hspan] at hh
  let : (F.terminalDot K).Normal := Normal.map hnK _ (QuotientGroup.mk'_surjective _)
  have hnsolv : ¬ Group.IsSolvable F.TerminalHdot := by
    intro hs
    let := hs
    let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
      ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 5))
      (Group.isSolvable_of_surjective (f := e5.toMonoidHom) e5.surjective)
  exact Recognition.rankTwo_center_eq_point_of_five_point h F d hne g hgP hgH hyp
    hnsolv (F.terminalDot K) e5 p hp he c hc hd

/-- The original closure has order 32 and is extraspecial; the literal
terminal-action kernel is the point normalizer's two-core. -/
theorem source_single_a5_extraspecial_of_four
    (e5 : F.terminalDot K ≃* alternatingGroup (Fin 5))
    (hspan : K = conjugateSpanBy K (T : Subgroup G))
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4) :
    F.ZU = F.Vi 1 ∧ IsExtraspecial 2 F.U ∧ Nat.card F.U = 32 ∧
      F.terminalHatAction.ker = pCore 2 F.H := by
  have hZ := source_single_a5_center_eq_point_of_four hG T hempty hM hu hmany
    hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  let d := Recognition.rankTwo_closure_geometry h F hne
  let he := Recognition.extraspecial_of_center_point F d (by decide) hZ hne
  let := he
  have hhat : Nat.card F.Uhat = 16 := by
    change Nat.card (Additive F.Uhat) = 16
    norm_num [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,hd]
  have hU : Nat.card F.U = 32 := by
    have hh := (center F.U).card_eq_card_quotient_mul_card_subgroup
    rw [IsExtraspecial.center_order_p 2 F.U,hhat] at hh
    exact hh
  exact ⟨hZ,he,hU,Recognition.terminal_kernel_of_center_point F d hZ⟩

end Source
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
