module

public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.Recognition.Core
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.PrimeComplement
public import Theory.GroupTheory.CComponent.RankTwoResidual
public import Theory.SpecificGroups.BinaryLinear.OuterTwo
public import Theory.SpecificGroups.Classical.BinaryLinearThreeRank

/-!
# The binary component as the original cubic residual

For either marked binary row L₄(2) or L₅(2), the actual core-to-star map
identifies X/O₂(X) with the centerless linear group. Its cubic rank is two
and its outer automorphism group is a two-group. The rank bound in the
original escaped I therefore gives X = O^{3′}(I), including relative
normality. No ambient normality in G is asserted.

The original K = O²(H) is a two-perfect {2,3}-group contained in I, so
K ≤ O^{3′}(I) = X. Its earlier centralization of ZS then puts K inside
M₁ = C_X(ZS). These are the residual and placement premises consumed by
the terminal module argument; the exhaustive marked catalogue is separate.

Source: Aschbacher--Smith, 15.2.23, printed pp.1116--1117, and A.3.18;
refs/quasithin.pdf.
-/

public section

open Subgroup Stellmacher Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
open Section01 PlaneUniquenessPreceding TerminalLinear
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include hsource

/-- The actual selected binary component is the cubic residual of I.
The quotient comparison uses the original C.2.7 core-to-star map. -/
theorem binary_eq_threeResidual
    (hI : PlaneEscapes Mc ZS I) {n : ℕ} (b : BinaryBranch M I X n) :
    X = (primeToResidual 3 I).map I.subtype := by
  have hn := b.degree
  let Y := X.subgroupOf I
  let eY : Y ≃* X := subgroupOfEquivOfLe b.source.component.1
  let eQ : (Y ⧸ pCore 2 Y) ≃* (X ⧸ pCore 2 X) :=
    QuotientGroup.congr _ _ eY (pCore_map_iso 2 eY)
  obtain ⟨eP,_⟩ := b.parabolic
  let e : (Y ⧸ pCore 2 Y) ≃* SL(n,ZMod 2) :=
    ((eQ.trans b.coreStarEquiv).trans eP).trans
      (BinaryLinear.OuterCyclic.projectiveEquivSL (by omega))
  let : IsQuasisimple (X ⧸ pCore 2 X) := b.source.quasisimple
  let : IsQuasisimple (Y ⧸ pCore 2 Y) := IsQuasisimple.of_mulEquiv eQ.symm
  have hz : center (Y ⧸ pCore 2 Y) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have he := ((centerCongr e) ⟨x,hx⟩).property
    change e x ∈ center SL(n,ZMod 2) at he
    rw [BinaryLinear.OuterCyclic.binary_center_eq_bot (by omega),mem_bot] at he
    exact e.map_eq_one_iff.mp he
  have hr : 2 ≤ primeRank 3 (Y ⧸ pCore 2 Y) := by
    rw [primeRank_congr 3 e]
    exact Theory.SpecificGroups.Classical.BinaryLinearThreeRank.two_le_primeRank (by omega)
  have ho : IsPGroup 2 (MulAut.Outer (Y ⧸ pCore 2 Y)) :=
    (BinaryLinear.OuterCyclic.sl_outer_isTwoGroup b.degree).of_equiv
      (MulAut.outerCongr e).symm
  have hY := b.source.component.2.eq_primeToResidual_three_of_rank_outer_two hz hr
    ((Chapter1.RadicalExclusions.sqtk_of_mem_H hsource.ambient hI.1).stronglyQuasithin
      3 Nat.prime_three (by decide)) ho
  have hh := congrArg (Subgroup.map I.subtype) hY
  rwa [map_subgroupOf_eq_of_le b.source.component.1] at hh

include d in
/-- The embedded O²(H) lies in the cubic residual, using its actual
{2,3}-structure and its already established containment in I. -/
theorem residual_le_threeResidual (hI : PlaneEscapes Mc ZS I) :
    (pResidual 2 H).map H.subtype ≤ (primeToResidual 3 I).map I.subtype := by
  obtain ⟨eH⟩ := d.geometry.quotient
  have hpi := ChosenGeometry.twoThree_of_wreath H eH
  let K := (pResidual 2 H).map H.subtype
  have hKI : K ≤ I := le_sup_left.trans
    ((d.residual_sup_planeSylow_le hI).trans inf_le_right)
  let K' := K.subgroupOf I
  let e : (pResidual 2 H) ≃* K' :=
    ((pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective).trans
      (subgroupOfEquivOfLe hKI).symm
  have hp : IsPPerfect 2 K' := (isPPerfect_pResidual 2 (G := H)).of_surjective
    e.toMonoidHom e.surjective
  have hKpi : IsPiGroup twoThreePrimes K' :=
    (hpi.of_injective (pResidual 2 H).subtype (pResidual 2 H).subtype_injective).of_equiv e.symm
  have hr : primeToResidual 3 K' = ⊤ := by
    rw [← twoResidual_eq_primeToResidual_three hKpi]
    exact (pResidual_eq_top_iff 2 K').mpr hp
  have hh := map_mono (f := I.subtype) (le_primeToResidual_of_eq_top 3 K' hr)
  rwa [map_subgroupOf_eq_of_le hKI] at hh

/-- Normality is relative to the original I. -/
theorem binary_normalized
    (hI : PlaneEscapes Mc ZS I) {n : ℕ} (b : BinaryBranch M I X n) :
    I ≤ normalizer (X : Set G) := by
  rw [binary_eq_threeResidual (hsource := hsource) hI b]
  exact I.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image I (primeToResidual 3 I))

include d in
/-- The original K lies in the literal plane centralizer of X. -/
theorem binary_residual_le_M1
    (hI : PlaneEscapes Mc ZS I) {n : ℕ} (b : BinaryBranch M I X n) :
    (pResidual 2 H).map H.subtype ≤ M1 X ZS := by
  refine le_inf ?_ d.residual_centralizes
  rw [binary_eq_threeResidual (hsource := hsource) hI b]
  exact residual_le_threeResidual d hI

end CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
