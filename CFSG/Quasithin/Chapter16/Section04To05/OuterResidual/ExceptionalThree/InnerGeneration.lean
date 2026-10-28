module

public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.ExceptionalThree.Transfer
public import Theory.GroupAction.PGroupFixedLift
public import Theory.NumberTheory.BinarySignedTorus

/-!
# Inner exceptional residuals: cover and generation transfers

A two-group model centralizer lifts through the actual central quotient
because the component center is a two-group. This proves the small-endpoint
deduction once its PSL₃(4) matrix calculation is supplied, including the
permitted nonsimple covers. No surjectivity on centralizers is assumed.

For the large endpoint, intrinsic containment of the residual two-core in
one O^{p′}, for p > 3, combines with the ordinary 16.4.5 identities and the
shared three-residual transfer. The linear and unitary model calculations
must still supply this intrinsic generation and the prime-rank bounds.
The arithmetic for the exact signed torus quotient is re-exported here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the inner
subcase of 16.4.8, printed p.1188. These are conditional transfers, not an
assertion that the model calculations or source branch are complete.
-/

public section

namespace CFSG.Quasithin.Chapter16.Intersections.OuterResidual.ExceptionalThree.InnerGeneration

open Subgroup Theory.GroupTheory
open ComponentTransfer

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

/-- A two-group fixed subgroup in the actual quotient model implies that
the full component centralizer is a two-group, even for a central cover. -/
theorem centralizer_isTwoGroup_of_model_fixed
    {𝒦 : GroupClass} (hG : Hypothesis1611 𝒦 G)
    (h : IntersectionSetup T z L g R) (hr : r ∈ R)
    {M : Type*} [Group M] (e : (L ⧸ center L) ≃* M)
    (hfixed : IsPGroup 2
      (MulAut.centralQuotientAction e (involutionAction h hr)).fixedSubgroup) :
    IsPGroup 2 (centralizerIn L r) := by
  let a := involutionAction h hr
  let b := MulAut.centralQuotientAction e a
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
  have hker : f.ker = center L := by
    ext x
    change e (QuotientGroup.mk' (center L) x) = 1 ↔ x ∈ center L
    rw [← map_one e, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  have htwo : IsPGroup 2 f.ker := by
    rw [hker, hG.evenType.component_center_eq_twoCore h.involution h.component]
    exact pCore_isPGroup
  have heq (x : L) : f (a x) = b (f x) :=
    (MulAut.centralQuotientAction_apply e a x).symm
  have ha := MulAut.isPGroup_fixedSubgroup_of_compatible a b f htwo heq hfixed
  exact ha.of_equiv
    (ComponentTransfer.Intrinsic.centralizerEquivFixed
      (h.sylow_normalizes (h.le_sylow hr))).symm

/-- The small model calculation suffices to kill the actual embedded
two-residual, including every source-permitted central cover. -/
theorem involutionResidual_eq_bot_of_model_fixed
    {𝒦 : GroupClass} (hG : Hypothesis1611 𝒦 G)
    (h : IntersectionSetup T z L g R) (hr : r ∈ R)
    {M : Type*} [Group M] (e : (L ⧸ center L) ≃* M)
    (hfixed : IsPGroup 2
      (MulAut.centralQuotientAction e (involutionAction h hr)).fixedSubgroup) :
    involutionResidual L r = ⊥ :=
  involutionResidual_eq_bot_of_isPGroup L r
    (centralizer_isTwoGroup_of_model_fixed hG h hr e hfixed)

/-- Intrinsic root-group generation supplies the two-core placement needed
by the three-residual transfer. The ordinary source 16.4.5 identities are
used only for primes strictly greater than three. -/
theorem threeResidual_le_conjugate_of_intrinsic_generation
    (h : IntersectionSetup T z L g R) (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hodd : Odd (pCore 2 (involutionResidual L r)).index)
    (hrank : ∀ p : ℕ, p.Prime → 3 < p → p ∣ Nat.card (involutionResidual L r) →
      1 < primeRank p L)
    (hgen : ∃ p : ℕ, p.Prime ∧ 3 < p ∧ p ∣ Nat.card (involutionResidual L r) ∧
      pCore 2 (involutionResidual L r) ≤ primeToResidual p (involutionResidual L r))
    (hres : ∀ p ∈ residualPrimes (L.conjBy g), 3 < p →
      (primeToResidual p (involutionCentralizer r)).map
        (involutionCentralizer r).subtype = L.conjBy g) :
    (pResidual 3 (involutionResidual L r)).map
      (involutionResidual L r).subtype ≤ L.conjBy g := by
  obtain ⟨p, hp, hp3, hpd, hcore⟩ := hgen
  have hpL : p ∈ residualPrimes (L.conjBy g) := by
    rw [residualPrimes_conjBy]
    exact ⟨hp, hp.odd_of_ne_two (by omega), hrank p hp hp3 hpd⟩
  have htwo : (pCore 2 (involutionResidual L r)).map
      (involutionResidual L r).subtype ≤ L.conjBy g :=
    (map_mono hcore).trans
      ((embedded_primeToResidual_mono p
        ((involutionResidual_le L r).trans inf_le_right)).trans
          (hres p hpL hp3).le)
  exact threeResidual_le_conjugate_of_twoCore h hr hr2 hodd htwo hrank hres

end CFSG.Quasithin.Chapter16.Intersections.OuterResidual.ExceptionalThree.InnerGeneration
