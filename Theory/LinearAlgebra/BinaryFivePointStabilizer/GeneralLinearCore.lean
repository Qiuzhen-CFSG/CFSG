module

public import Theory.PGroupCore
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# The two-core of the full binary linear group

The full linear automorphism group of a four-dimensional binary vector space
has trivial two-core. A two-group acting on the sixteen vectors has a nonzero
fixed vector, since zero is fixed. Linear automorphisms act transitively on the
nonzero vectors: an isomorphism of their spans extends to the ambient space.
Normality of the two-core therefore makes every vector fixed, so its elements
are the identity.

This supplies the quotient-core calculation for the binary five-dimensional
point stabilizer in Aschbacher--Smith, *The Classification of Quasithin Groups*,
Lemma 14.2.21, printed p.989 (PDF p.1006).
-/

namespace Theory.LinearAlgebra.BinaryFivePointStabilizer

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem transitive_nonzero (x y : V) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ g : V ≃ₗ[ZMod 2] V, g x = y := by
  let ex := LinearEquiv.toSpanNonzeroSingleton (ZMod 2) V x hx
  let ey := LinearEquiv.toSpanNonzeroSingleton (ZMod 2) V y hy
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq (ex.symm.trans ey)
  refine ⟨g, ?_⟩
  have h := hg (ex 1)
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at h
  simpa [ex, ey] using h.symm

/-- The full linear automorphism group of a four-dimensional binary space has
trivial two-core. -/
public theorem pCore_eq_bot_finrank_four [FiniteDimensional (ZMod 2) V]
    (hV : Module.finrank (ZMod 2) V = 4) :
    pCore 2 (V ≃ₗ[ZMod 2] V) = ⊥ := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let N := pCore 2 (V ≃ₗ[ZMod 2] V)
  have hcard : 2 ∣ Nat.card V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hV]
    decide
  have hzero : (0 : V) ∈ MulAction.fixedPoints N V := by
    intro g
    exact map_zero (g.val)
  have hN : IsPGroup 2 N := pCore_isPGroup
  obtain ⟨v, hv, hv0⟩ :=
    hN.exists_fixed_point_of_prime_dvd_card_of_fixed_point V hcard hzero
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro n hn
  apply LinearEquiv.ext
  intro w
  change n w = w
  by_cases hw : w = 0
  · rw [hw, map_zero]
  obtain ⟨g, hg⟩ := transitive_nonzero v w (Ne.symm hv0) hw
  have hconj : g⁻¹ * n * g ∈ N :=
    (inferInstance : N.Normal).conj_mem' n hn g
  have hfix := hv ⟨g⁻¹ * n * g, hconj⟩
  change g.symm (n (g v)) = v at hfix
  have heq := congrArg g hfix
  simpa only [LinearEquiv.apply_symm_apply, hg] using heq

end Theory.LinearAlgebra.BinaryFivePointStabilizer
