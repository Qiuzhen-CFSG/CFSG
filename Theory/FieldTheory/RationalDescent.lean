module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Classification
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Rational descent for algebraic complex numbers

Every automorphism of a field extends to any algebraically closed overfield:
choose a transcendence basis, act on polynomial coefficients, and extend
across the resulting algebraic closures. Apply this to the algebraic numbers
inside `ℂ`. Their Galois fixed-field theorem then shows that an algebraic
complex number fixed by all field automorphisms of `ℂ` is rational.

The argument does not assume that `ℂ/ℚ` is algebraic. It supplies the descent
step for unique-degree character rationality (Wong (1964), Appendix (b), p. 109).
-/

public section

noncomputable section

namespace IsAlgClosed

/-- A field automorphism extends to any algebraically closed overfield. -/
theorem exists_ringEquiv_extension {K L : Type*} [Field K] [Field L] [Algebra K L]
    [IsAlgClosed L] (σ : K ≃+* K) :
    ∃ τ : L ≃+* L, ∀ x : K, τ (algebraMap K L x) = algebraMap K L (σ x) := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis K L
  let A := Algebra.adjoin K (Set.range ((↑) : s → L))
  let e : MvPolynomial s K ≃ₐ[K] A := hs.1.aevalEquiv
  let f : A ≃+* A := e.symm.toRingEquiv.trans ((MvPolynomial.mapEquiv s σ).trans e.toRingEquiv)
  let := isAlgClosure_of_transcendence_basis ((↑) : s → L) hs
  refine ⟨IsAlgClosure.equivOfEquiv L L f, ?_⟩
  intro x
  have hf : f (algebraMap K A x) = algebraMap K A (σ x) := by
    change e (MvPolynomial.map σ (e.symm (algebraMap K A x))) = _
    rw [e.symm.commutes]
    simpa using e.commutes (σ x)
  change IsAlgClosure.equivOfEquiv L L f (algebraMap A L (algebraMap K A x)) = _
  rw [IsAlgClosure.equivOfEquiv_algebraMap, hf]
  rfl

end IsAlgClosed

/-- An algebraic complex number fixed by all field automorphisms is rational. -/
theorem Complex.exists_ratCast_of_isAlgebraic_of_fixed {z : ℂ} (hz : IsAlgebraic ℚ z)
    (hfix : ∀ σ : ℂ ≃+* ℂ, σ z = z) : ∃ q : ℚ, z = (q : ℂ) := by
  let K := algebraicClosure ℚ ℂ
  let : IsAlgClosure ℚ K := algebraicClosure.isAlgClosure ℚ ℂ
  let a : K := ⟨z, mem_algebraicClosure_iff.mpr hz⟩
  have ha : ∀ σ : K ≃ₐ[ℚ] K, σ a = a := by
    intro σ
    obtain ⟨τ, hτ⟩ := IsAlgClosed.exists_ringEquiv_extension (L := ℂ) σ.toRingEquiv
    apply Subtype.ext
    exact (hτ a).symm.trans (hfix τ)
  obtain ⟨q, hq⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed a).mpr ha
  exact ⟨q, (congrArg (fun a : K => (a : ℂ)) hq).symm⟩
