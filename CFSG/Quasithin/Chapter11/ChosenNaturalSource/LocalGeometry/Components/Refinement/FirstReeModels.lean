module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.FirstExceptionalModels
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.Order.TorusCardinality
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups
public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree
public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.TitsSystem
public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.LinearRadical
public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.Opposition
public import Theory.GroupTheory.PerfectCenterFrattini

/-!
# Ree model facts for the first flag normalizer

The literal fixed torus has two independent coefficient-field unit factors.
Thus every prime divisor of q−1 gives rank at least two. A primitive divisor
is larger than the field degree and misses the actual outer group order.

The center calculation does not assume model simplicity. Perfectness puts
its center inside every maximal subgroup. The root-defined linear parabolic
is maximal by the proved BN-pair; its radical is self-centralizing and
misses the opposite parabolic, so its normal core is trivial. Consequently
the center is trivial. The consumer in FirstRee obtains perfectness and
quasisimplicity from the actual C-component, then deduces simplicity before
using the outer-automorphism theorem. No model-simplicity premise is added.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.1.2, printed pp.761--762, and A.3.18, printed pp.51--53.
The fixed torus and parabolic calculations retain the GLS3 references in
the imported construction modules.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.ExceptionalActors

/-- Perfectness and the actual core-free maximal parabolic force trivial center. -/
theorem ree_center_eq_bot_of_perfect {m : ℕ} (hm : 1 ≤ m)
    (d : ReeF4.LocalBlockInput m) [Group.IsPerfect d.fixedGroup] :
    center d.fixedGroup = ⊥ := by
  let : Group.IsPerfect (ReeF4.Model m) := Group.IsPerfect.ofSurjective
    (f := d.modelEquiv.toMonoidHom) d.modelEquiv.surjective
  obtain ⟨T, _, s, hs, hP⟩ := ReeF4.SectionGeometry.BNPair.exists_titsSystem m hm
  obtain ⟨P, hmax, hcore⟩ := ReeF4.SectionGeometry.exists_coreFree_coatom_of_geometry
    m .linear T s hs hP
    (ReeF4.SectionGeometry.LinearRadical.parabolic_le_radical_normalizer m .linear)
    (ReeF4.SectionGeometry.LinearRadical.centralizer_le_radical m hm)
    (ReeF4.SectionGeometry.Opposition.exists_linear_opposition m)
  have hz : center (ReeF4.Model m) = ⊥ := by
    apply bot_unique
    rw [← hcore]
    exact normal_le_normalCore.mpr
      (center_le_frattini_of_isPerfect.trans (frattini_le_coatom hmax))
  apply bot_unique
  intro z hz'
  exact d.modelEquiv.map_eq_one_iff.mp (hz.le
    ((centerCongr d.modelEquiv) ⟨z,hz'⟩).property)

/-- The literal fixed torus witnesses rank two at each split prime. -/
theorem ree_split_rank {m p : ℕ} [Fact p.Prime]
    (d : ReeF4.LocalBlockInput m) (hd : p ∣ 2 ^ (2 * m + 1) - 1) :
    2 ≤ primeRank p d.fixedGroup := by
  have hu : 1 ≤ primeRank p (ReeF4.CoefficientField m)ˣ := by
    by_contra hh
    have hz : primeRank p (ReeF4.CoefficientField m)ˣ = 0 := by omega
    apply PrimeRank.eq_zero_iff_not_dvd_card.mp hz
    simpa only [Nat.card_units, ReeF4.field_card] using hd
  have hi := primeRank_le_of_injective p
    (ReeF4.ConverseParabolics.FullLeviRepresentation.torusHom m)
    (ReeF4.ConverseParabolics.FullLeviRepresentation.torusHom_injective m)
  rw [primeRank_prod_eq_add] at hi
  rw [primeRank_equiv p d.modelEquiv]
  omega

/-- A prime larger than the coefficient-field degree cannot act through the outer group. -/
theorem ree_primitive_primePower_inner {m p : ℕ} (hm : 1 ≤ m)
    (d : ReeF4.LocalBlockInput m) [IsSimpleGroup d.fixedGroup]
    [Group.IsPerfect d.fixedGroup] (hp : p.Prime) (hpdeg : 2 * m + 1 < p)
    (a : MulAut d.fixedGroup) (k : ℕ) (ha : a ^ (p ^ k) = 1) :
    a ∈ MulAut.innerSubgroup d.fixedGroup :=
  outer_primePower_inner (ReeF4.LocalBlockInput.outer_card_dvd hm d)
    (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hpdeg)) a k ha

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.ExceptionalActors
