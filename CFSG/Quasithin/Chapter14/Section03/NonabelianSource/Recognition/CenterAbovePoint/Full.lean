module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.CenterAbovePoint.Linear
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.SmallCenterKernel
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Four.FullOrthogonal

/-!
# The full orthogonal action when the center exceeds the point

The actual center-conjugate residual excludes a faithful symmetric-pair
actor. The solvable degree-four Fitting alternative therefore has actor
rank two. Its quotient-rank bound makes the original tilded center a binary
line. The small-center kernel theorem and the original cubic-index
exclusion then exclude every normal cubic in the dotted actor, forcing
its prescribed orthogonal realization to have the full carrier. Both the
literal central quotient and the action-intertwining coordinates remain
those of the original selected invariant flag.

Source: Aschbacher--Smith 14.3.15, printed p.995, using 12.8.13(3) and G.9.4(4).
-/

public section
open Subgroup Theory.GroupTheory Module
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G] {K : GroupClass}
variable {T : Sylow 2 G} {V : Subgroup G} {L M : Subgroup G}
section Selected
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
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
    (g : G) [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hZ : F.ZU ≠ F.Vi 1)
include hG hempty hM hu hmany hcard e hnot F d hne g hgP hgH hyp hZ

/-- Degree four and actor rank two make the original tilded center a binary
line. The bound is on its literal quotient image. -/
theorem tilde_center_card_le_two_of_center_ne_point
    (cover : Nonempty (ChapterG.Section09.SQTKCover KnownSimple.IsKnownSimple F.TerminalHdot))
    (hs : Group.IsSolvable F.TerminalHdot) : Nat.card (F.tilde F.ZU) ≤ 2 := by
  classical
  have hc := orthogonal_case_of_center_ne_point hG T hempty hM hu hmany hcard e hnot
    F d hne g hgP hgH hyp hZ cover hs
  let X := F.terminalDot (F.X g)
  let X₀ := (F.terminalDot (conjugate F.ZU g)).subgroupOf X
  have hX : Nat.card X = 4 := by
    change Nat.card (F.terminalDot (F.X g)) = _
    rw [Nat.card_congr Additive.ofMul,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hc.1]
    decide
  have hqpos : 0 < Group.rank (X ⧸ X₀) := by
    have hb := hyp.dimension_bound.1
    rw [hc.2.1] at hb
    change 4 ≤ 2 * (Group.rank (X ⧸ X₀) + 1) at hb
    omega
  have hsmall : Nat.card X₀ ≤ 2 := by
    have hd := X₀.card_subgroup_dvd_card
    rw [hX] at hd
    have hh := Nat.mem_divisors.mpr ⟨hd,by decide⟩
    have hdiv : (4 : ℕ).divisors = {1,2,4} := by decide
    rw [hdiv,Finset.mem_insert,Finset.mem_insert,Finset.mem_singleton] at hh
    rcases hh with h1 | h2 | h4
    · omega
    · omega
    · have ht : X₀ = ⊤ := eq_of_le_of_card_ge le_top (by rw [card_top,hX,h4])
      have hr : Group.rank (X ⧸ X₀) = 0 := by
        rw [ht]
        let : Subsingleton (X ⧸ (⊤ : Subgroup X)) := QuotientGroup.subsingleton_quotient_top
        exact Group.rank_eq_zero _
      omega
  have hZle : F.terminalDot (conjugate F.ZU g) ≤ X :=
    map_mono (comap_mono (F.conjugate_ZU_le_X g))
  have hZH : F.ZU ≤ F.H := (map_subtype_le (center F.U)).trans F.U_le_H
  let ee := (rankTwo_terminal_center_equiv
    (source_lemma_14_2_4 hG T hempty hM hu hmany hcard e) F d hne g hgP hgH).symm.trans
      (F.terminalCenterTildeEquiv hZH)
  rw [←Nat.card_congr ee.toEquiv]
  exact (Nat.card_congr (subgroupOfEquivOfLe hZle).toEquiv).symm ▸ hsmall

/-- The proper orthogonal alternative is excluded by the actual small-center
kernel and original cubic-index theorem, without a global recognition premise. -/
theorem full_orthogonal_of_center_ne_point
    (cover : Nonempty (ChapterG.Section09.SQTKCover KnownSimple.IsKnownSimple F.TerminalHdot))
    (hs : Group.IsSolvable F.TerminalHdot) :
    ChapterG.Section09.FittingRecognition.OrthogonalRealization F.terminalRepresentation ⊤ := by
  have hc := orthogonal_case_of_center_ne_point hG T hempty hM hu hmany hcard e hnot
    F d hne g hgP hgH hyp hZ cover hs
  have hk := terminal_kernel_isPGroup_of_tilde_center_card_le_two F d
    (tilde_center_card_le_two_of_center_ne_point hG T hempty hM hu hmany hcard e hnot
      F d hne g hgP hgH hyp hZ cover hs)
  have hA : Nat.card (F.terminalDot (F.X g)) = 4 := by
    rw [Nat.card_congr Additive.ofMul,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hc.1]
    decide
  apply hc.full_orthogonal_of_no_normal_cubic (F.terminalDot (F.X g)) hA
  intro C hCn hCc
  let := hCn
  exact no_normal_cubic_of_two_kernel hG T hempty hM hu hmany hcard e hnot F d hk C hCc

end Selected
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
