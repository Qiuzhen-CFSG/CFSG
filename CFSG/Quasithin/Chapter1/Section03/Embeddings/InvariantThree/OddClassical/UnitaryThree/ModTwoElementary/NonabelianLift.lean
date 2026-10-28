module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.UnitaryThree.ModTwoElementary.ModelCases
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.UnitaryThree.ModTwoElementary.NonabelianLift.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.UnitaryThree.ModTwoElementary.NonabelianLift.Placement
public import Theory.SpecificGroups.SU3.OddThreeLocal.Monomial.LocalCore

/-!
# The nonabelian special-unitary lift of an elementary projective pair

A genuine monomial placement of the full special preimage permits the
special-unitary three-core calculation. The lifted product has three-part 27;
its core has order nine. Descent through the scalar kernel gives a projective
core of order three. Its intersection with U is the invariant line for every
two-subgroup of the full pair automizer, including outer automorphisms.

The final theorem supplies the geometric placement and the special monomial
core calculation for odd primes p > 3 with p ≡ 2 modulo three. This completes
the nonabelian-lift case while retaining the actual projective unitary model
and its inherited simplicity hypothesis.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511 (PDF p.528),
and A.3.21(c), printed pp.55–56; GLS3, Theorem 6.5.3(b),
`refs/KGroup/GLS3/chapter6.tex`.
-/

public section
open Subgroup BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.UnitaryThree.ModTwoElementary

/-- Conditional full pair-action reducibility, retaining precisely the two
remaining geometric and monomial inputs. -/
theorem nonabelian_lift_reducibility_of_monomial
    (p : ℕ) (hplacement : NonabelianLift.MonomialPlacement p)
    (hcore : ∀ {E : Type} [Field E] [Finite E] (J : HermitianForm 3 E),
      Nat.card E = p ^ 2 → (∀ x, J.conj x = x ^ p) → J.form = 1 →
      ∀ (S : Sylow 2 J.specialSubgroup) (H : Subgroup J.specialSubgroup),
        (S : Subgroup J.specialSubgroup) ≤ H →
        H ≤ HermitianForm.OddThreeLocal.Monomial.special J →
        Nat.card H = 27 * Nat.card S →
        (∃ R : Subgroup J.specialSubgroup,
          R ≤ H ∧ IsPGroup 3 R ∧ ¬ IsMulCommutative R) →
        Nat.card (pCore 3 H) = 9) : NonabelianLiftReducibility p := by
  intro E _ _ J hs hE hconj T U he hc hn hperm
  obtain ⟨J', hconj', hJ', e, hle⟩ := hplacement J hs hE hconj T U he hc hn hperm
  obtain ⟨S, hS, hScard⟩ := NonabelianLift.exists_special_sylow J T
  let H := (U ⊔ (T : Subgroup _)).comap J.specialToProjective
  have hSH : (S : Subgroup J.specialSubgroup) ≤ H := by
    apply map_le_iff_le_comap.mp
    rw [hS]
    exact le_sup_right
  let S' := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hScard' : Nat.card S' = Nat.card T := by
    change Nat.card ((S : Subgroup J.specialSubgroup).map e.toMonoidHom) = _
    rw [card_map_of_injective e.injective]
    exact hScard
  have hHcard : Nat.card (H.map e.toMonoidHom) = 27 * Nat.card S' := by
    rw [card_map_of_injective e.injective, hScard']
    exact NonabelianLift.preimage_product_card J T U he hc hperm hn
  have hR : ∃ R : Subgroup J'.specialSubgroup,
      R ≤ H.map e.toMonoidHom ∧ IsPGroup 3 R ∧ ¬ IsMulCommutative R := by
    let R := U.comap J.specialToProjective
    refine ⟨R.map e.toMonoidHom, map_mono (comap_mono le_sup_left),
      ((NonabelianLift.preimage_three_group_card J U he hc hn).1).map e.toMonoidHom, ?_⟩
    intro hab
    let _ := hab
    let eR := R.equivMapOfInjective e.toMonoidHom e.injective
    exact hn (.of_comm fun x y => eR.injective (by
      rw [map_mul, map_mul]
      exact mul_comm' _ _))
  have hcount := hcore J' hE hconj' hJ' S' (H.map e.toMonoidHom)
    (map_mono hSH) hle hHcard hR
  have hcount' : Nat.card (pCore 3 H) = 9 := by
    let eH := e.subgroupMap H
    have hh := Nat.card_congr ((eH.subgroupMap (pCore 3 H)).trans
      (MulEquiv.subgroupCongr (pCore_map_iso 3 eH))).toEquiv
    exact hh.trans hcount
  exact NonabelianLift.reducible_of_special_core_nine J T U he hc hperm hn hcount'

/-- Every two-subgroup of the full pair automizer is reducible when the
elementary projective order-nine subgroup has nonabelian special-unitary
preimage. The intrinsic projective three-core supplies a common invariant line. -/
theorem nonabelian_lift_reducibility
    (p : ℕ) (hp : p.Prime) (ho : Odd p) (hlarge : 3 < p)
    (hmod : p % 3 = 2) : NonabelianLiftReducibility p := by
  apply nonabelian_lift_reducibility_of_monomial p
    (NonabelianLift.monomial_placement p hp ho hlarge hmod)
  intro E _ _ J hE hconj hJ
  exact HermitianForm.OddThreeLocal.Monomial.special_core_card_nine
    J hp ho hlarge hmod hE hconj hJ

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.UnitaryThree.ModTwoElementary
