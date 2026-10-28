module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.CenterAbovePoint.Cohomology
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.CenterAbovePoint.Geometry
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.ActorRankIntersection
public import Theory.Representation.BinaryPermutation.FivePointNormal

/-!
# The original center is the point in the full five-point case

The literal W-hat has dimension three and is invariant under the actual
dotted Sylow subgroup. A nontrivial displaced center must move it in the
faithful five-point action. The source commutator bound then identifies
the commutator with the displaced point. The normal-subgroup H¹ theorem
and the central-cover criterion prove Z(U)=V₁.

This result retains the selected normal A₅, full dotted action and all
original quotient conventions. It supplies local extraspecial geometry;
it does not assert ambient Janko recognition.

Source: Aschbacher–Smith 14.3.14–15 and I.1.5–6, pp.993–995,408.
-/

public noncomputable section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
variable {G : Type*} [Group G] [Finite G] {κ : GroupClass}
    {T : Sylow 2 G} {L M : Subgroup G}
    (h : RankTwoHypothesis κ T L M)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (d : ClosureGeometry F) (hne : ¬ IsMulCommutative F.U)
    (g : G) [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hnsolv : ¬ Group.IsSolvable F.TerminalHdot)
    (D : Subgroup F.TerminalHdot) [D.Normal] (e5 : D ≃* alternatingGroup (Fin 5))
    (p : F.TerminalHdot →* Equiv.Perm (Fin 5)) (hp : Function.Injective p)
    (he : ∀ l : D, p l = (e5 l).val)
    (c : Additive F.Uhat ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 5))
    (hc : ∀ a w, c (F.terminalRepresentation a w) =
      BinaryPermutation.coreRepresentation (Fin 5) (p a) (c w))
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4)
include h d hne hgP hgH hyp hp he hc hd

omit hyp [IsElementaryAbelian 2 (F.terminalDot (F.X g))] in
/-- In the original degree-four five-point action, the displaced center
moves the Sylow-invariant hyperplane whenever the center exceeds the point. -/
theorem rankTwo_five_point_center_commutator (hZ : F.ZU ≠ F.Vi 1) :
    ⁅F.W,conjugate F.ZU g⁆ = conjugate (F.Vi 1) g := by
  have hnat : 3 ≤ 2 → Nonempty (AmbientNaturalMarking L h.L_normalizes_seed 2) := by omega
  obtain ⟨hcomm,_⟩ := F.localKernel_commutator_squares h.simpleQTKE L M (by decide)
    h.seed_le_sylow h.L_normalizes_seed h.sylow_normalizes_L h.L_residual hnat (h.flag_escape F)
  let form := F.localKernel_markedForm (by decide) d.two d.frattini_point hcomm
  have hq := F.finrank_quotient_hat_centralizer (by decide) d.seed_center form
  have hdim := (hatSpace F F.W).finrank_quotient_add_finrank
  change finrank (ZMod 2) (Additive F.Uhat ⧸ hatSpace F F.W) = 1 at hq
  have hw : finrank (ZMod 2) (hatSpace F F.W) = 3 := by omega
  have hTW : (T : Subgroup G) ≤ normalizer (F.W : Set G) :=
    (le_inf ((F.invariant 1).trans (le_normalizer_conjugateSpanBy _ F.H))
      ((F.invariant 2).trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  let R : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
    (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
  have hstable : ∀ a ∈ R, ∀ w ∈ hatSpace F F.W,
      F.terminalRepresentation a w ∈ hatSpace F F.W :=
    F.terminal_hatSpace_invariant F.W (T : Subgroup G) hTW
  have hneZ := F.terminalDot_center_ne_bot g
    (F.conjugate_center_le_H g (F.P_le_seed_normalizer L h.L_normalizes_seed hgP))
    (rankTwo_terminal_center_kernel h F d hne g hgP hgH)
    (lt_of_le_of_ne (F.point_le_ZU (by decide)) (Ne.symm hZ))
  obtain ⟨a,ha,hane⟩ := ((F.terminalDot (conjugate F.ZU g)).bot_or_exists_ne_one).resolve_left hneZ
  have hm : ∃ w ∈ hatSpace F F.W, F.terminalRepresentation a w ≠ w := by
    by_contra hh
    push Not at hh
    exact hane (BinaryPermutation.FivePointNormal.hyperplane_fixer_eq_one
      F.terminalRepresentation D e5 p hp he c hc R (hatSpace F F.W) hw hstable a hh)
  obtain ⟨w,hwW,hwmove⟩ := hm
  have hn : ⁅F.W,conjugate F.ZU g⁆ ≠ ⊥ := by
    intro hb
    have hcent : conjugate F.ZU g ≤ centralizer (F.W : Set G) := by
      rw [commutator_comm] at hb
      exact commutator_eq_bot_iff_le_centralizer.mp hb
    obtain ⟨a,ha,rfl⟩ := ha
    obtain ⟨u,hu,heu⟩ := (show w.toMul ∈ hatImage F F.W from hwW)
    apply hwmove
    apply Additive.toMul.injective
    rw [F.terminalRepresentation_apply_mk,←heu,F.terminalHatAction_apply_mk]
    apply congrArg (QuotientGroup.mk' (center F.U))
    apply Subtype.ext
    change (a : G) * (u : G) * (a : G)⁻¹ = (u : G)
    have he : (u : G) * (a : G) = (a : G) * (u : G) := mem_centralizer_iff.mp (hcent ha) u hu
    rw [←he,mul_assoc,mul_inv_cancel,mul_one]
  have hcard : Nat.card (conjugate (F.Vi 1) g) = 2 := by
    rw [conjugate,card_map_of_injective (MulAut.conj g⁻¹).injective]
    simpa using F.card 1 (by decide)
  apply eq_of_le_of_card_ge (rankTwo_center_commutator_le_conjugate_point h F d hne g hgP hgH)
  rw [hcard]
  have hh := (one_lt_card_iff_ne_bot ⁅F.W,conjugate F.ZU g⁆).mpr hn
  omega

include hnsolv in
/-- The original center is the marked point for a faithful full five-point
module containing the same normal alternating component. -/
theorem rankTwo_center_eq_point_of_five_point : F.ZU = F.Vi 1 := by
  apply rankTwo_center_eq_point_of_normal_cohomology h F d hne g hgP hgH hyp hnsolv
  · exact rankTwo_five_point_center_commutator h F d hne g hgP hgH D e5 p hp he c hc hd
  · intro A hA hneA
    let n := BinaryPermutation.coreEquivNatural (Fin 5) (by decide)
    apply BinaryPermutation.FivePointNormal.normal_dual_H1_zero
      F.terminalRepresentation D e5 p hp he (c.trans n) ?_ A hneA
    intro a w
    change n (c (F.terminalRepresentation a w)) = _
    rw [hc]
    exact BinaryPermutation.coreEquivNatural_equivariant (Fin 5) (by decide) (p a) (c w)
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
