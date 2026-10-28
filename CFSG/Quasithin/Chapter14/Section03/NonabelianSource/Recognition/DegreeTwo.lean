module
public import Theory.Representation.BinaryPlaneCubic
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.SmallCenterKernel
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.NumericalGeometry
public import CFSG.Quasithin.ChapterG.Section10.TwoCore

/-!
# The original degree-two exclusion

A faithful binary plane action bounds the displaced center by order two.
The original center-quotient equivalence transfers that bound to the tilded
center, making the dotted action kernel a two-group. The normal cubic in
this plane group now lifts to an overgroup of Sylow index three, contrary
to the original selected-source cubic theorem.

Source: Aschbacher--Smith 14.3.13, printed pp.993--994.
-/

public section
open Subgroup Module Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original degree-two terminal action is impossible. -/
theorem false_of_degree_two
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (d : ClosureGeometry F) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat)
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v (hatSpace F (F.E g))
      (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 2) : False := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  have hZH : F.ZU ≤ F.H := (map_subtype_le (center F.U)).trans F.U_le_H
  have heq := (rankTwo_terminal_center_equiv h F d hne g hgP hgH).symm.trans
    (F.terminalCenterTildeEquiv hZH)
  have hz2 : IsPGroup 2 (F.terminalDot (conjugate F.ZU g)) :=
    (IsElementaryAbelian.isPGroup 2 (F.terminalDot (F.X g))).to_le
      (map_mono (comap_mono (F.conjugate_ZU_le_X g)))
  have hcZ : Nat.card (F.tilde F.ZU) ≤ 2 := by
    rw [← Nat.card_congr heq.toEquiv]
    exact Representation.BinaryPlane.two_subgroup_card_le_two
      F.terminalRepresentation F.terminalRepresentation_injective hd _ hz2
  have hk2 := terminal_kernel_isPGroup_of_tilde_center_card_le_two F d hcZ
  let : Nontrivial F.TerminalHdot := by
    by_contra hn
    let : Subsingleton F.TerminalHdot := not_nontrivial_iff_subsingleton.mp hn
    have hs : Submodule.span (ZMod 2) {v} = ⊤ := by
      apply top_unique
      rw [← hyp.orbit_span]
      apply Submodule.span_le.mpr
      rintro _ ⟨a,rfl⟩
      have ha : F.terminalRepresentation a v = v := by
        rw [Subsingleton.elim a (1:F.TerminalHdot),map_one]
        rfl
      rw [ha]
      exact Submodule.mem_span_singleton_self v (R := ZMod 2)
    have hh := finrank_span_singleton (K := ZMod 2) hyp.point_ne_zero
    rw [hs,finrank_top,hd] at hh
    omega
  obtain ⟨C,hCn,hCc⟩ := Representation.BinaryPlane.exists_normal_cubic
    F.terminalRepresentation F.terminalRepresentation_injective hd hyp.twoCore_eq_bot
  let := hCn
  exact no_normal_cubic_of_two_kernel hG T hempty hM hu hmany hcard e hnot F d hk2 C hCc

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
