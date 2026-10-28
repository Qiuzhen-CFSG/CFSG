module

public import Theory.AlgebraicGroup.Automorphisms.Lang.root_subgroup_fixed_count

/-!
# Nonidentity periodic root elements

The fixed-root count is strictly greater than one because the matrix-Frobenius
witness has positive exponent. Thus an invariant iterate has a nonidentity
fixed element in the given absolute root subgroup. The orbit-product consumer
then turns this periodic element into an element fixed by sigma itself.

This uses the proved fixed-count theorem, not the unresolved Steinberg to
Frobenius implication in `Lang.theorem_2_1_11`.

Source: GLS3, Proposition 2.1.10 and Theorem 2.1.12.
-/

namespace Theory.AlgebraicGroup.ProperParabolicFixedRadical

variable {k : Type*} [Field k] [IsAlgClosed k]
    {K : Variety k} [AlgebraicGroup K]
    {p : ℕ} [Fact p.Prime] [CharP k p]

omit [IsAlgClosed k] in
/-- The positive matrix-Frobenius exponent forces the level to exceed one. -/
public theorem frobeniusLevel_one_lt (σ : AlgebraicEndomorphism K) (q : NNReal)
    (hσ : IsFrobeniusEndomorphismOfLevel (r := p) q σ) : 1 < q := by
  obtain ⟨m, a, n, H, hm, ha, hq, _⟩ := hσ
  have hp : (1 : NNReal) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hpow : (1 : NNReal) < q ^ m := by
    rw [hq]
    exact one_lt_pow₀ hp ha.ne'
  exact (one_lt_pow_iff hm.ne').mp hpow

/-- Counting the fixed points of an invariant root subgroup produces a
nonidentity periodic element. An actual Frobenius-level witness is essential. -/
public theorem exists_nonidentity_fixed_root_iterate
    (σ : AlgebraicEndomorphism K) (q : NNReal)
    (hσ : IsFrobeniusEndomorphismOfLevel (r := p) q σ)
    (T X : ClosedSubgroup K) (hX : IsTorusRootSubgroup T X)
    (m : ℕ) (hm : 0 < m)
    (hmaps : Set.MapsTo (σ.onPoints^[m])
      (X : Set (Variety.Point K)) (X : Set (Variety.Point K)))
    (hsurj : Set.SurjOn (σ.onPoints^[m])
      (X : Set (Variety.Point K)) (X : Set (Variety.Point K))) :
    ∃ x : Variety.Point K, x ∈ X ∧ (σ.onPoints^[m]) x = x ∧ x ≠ 1 := by
  have hcount := rootSubgroup_fixedPoints_ncard_eq_level_pow σ q hσ T X hX
    m hm hmaps hsurj
  have hq := one_lt_pow₀ (frobeniusLevel_one_lt σ q hσ) hm.ne'
  have hc : 1 < Set.ncard {x : Variety.Point K |
      x ∈ X.toSubgroup ∧ (σ.onPoints^[m]) x = x} := by
    have : (1 : NNReal) <
        (Set.ncard {x : Variety.Point K |
          x ∈ X.toSubgroup ∧ (σ.onPoints^[m]) x = x} : NNReal) := by
      rw [hcount]
      exact hq
    exact_mod_cast this
  obtain ⟨x, hx, hne⟩ := Set.exists_ne_of_one_lt_ncard hc 1
  exact ⟨x, hx.1, hx.2, hne⟩

end Theory.AlgebraicGroup.ProperParabolicFixedRadical
