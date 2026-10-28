module

public import Theory.Representation.SL2.HighestWeight
public import Theory.Representation.SubrepresentationLattice

/-!
# Simple Highest-Weight Orbit Spans

For a field homomorphism `K -> F`, consider the actual polynomial action of
`SL2(K)` over `F`. The span of the orbit of `X 0 ^ n` is a finite-dimensional
subrepresentation contained in the degree-`n` homogeneous binary forms.

If `K` has `n + 1` distinct elements, this subrepresentation is irreducible.
Indeed, a nonzero invariant subspace contains a nonzero homogeneous form;
upper-transvection sampling extracts `X 0 ^ n`, whose orbit spans the entire
subrepresentation. In particular this holds for `n < |K|` when `K` is finite.
No characteristic restriction or tensor-product classification is assumed.

This supplies concrete candidates for the simple modules in Fong--Wong,
Nagoya Math. J. 36 (1969), p. 149, formula (1.15). Their dimensions, tensor
identifications, pairwise inequivalence, and exhaustivity are separate results.
The orbit-span definition is exposed for these subsequent basis computations.
-/

open MvPolynomial
open scoped MatrixGroups

namespace Representation.SL2

variable {K F : Type*} [Field K] [Field F]

@[expose] public noncomputable def highestWeightSpan (e : K →+* F) (n : ℕ) :
    Subrepresentation ((polynomialRepresentation F).comp (Matrix.SpecialLinearGroup.map e)) where
  toSubmodule := Submodule.span F (Set.range fun g : SL(2, K) =>
    polynomialAction F (Matrix.SpecialLinearGroup.map e g) (X 0 ^ n))
  apply_mem_toSubmodule g := by
    intro v hv
    let ρ := (polynomialRepresentation F).comp (Matrix.SpecialLinearGroup.map e)
    change ρ g v ∈ Submodule.span F (Set.range fun h : SL(2, K) => ρ h (X 0 ^ n))
    change v ∈ Submodule.span F (Set.range fun h : SL(2, K) => ρ h (X 0 ^ n)) at hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨h, rfl⟩ := hv
      rw [← Module.End.mul_apply, ← map_mul]
      exact Submodule.subset_span ⟨g*h, rfl⟩
    | zero => simp
    | add v w _ _ hv hw => simpa only [map_add] using Submodule.add_mem _ hv hw
    | smul c v _ hv => simpa only [map_smul] using Submodule.smul_mem _ c hv

public theorem X_pow_mem_highestWeightSpan (e : K →+* F) (n : ℕ) :
    X 0 ^ n ∈ highestWeightSpan e n := by
  apply Submodule.subset_span
  refine ⟨1, ?_⟩
  change ((polynomialRepresentation F).comp (Matrix.SpecialLinearGroup.map e)) 1 (X 0 ^ n) = _
  simp

public theorem highestWeightSpan_le_iff (e : K →+* F) (n : ℕ)
    (U : Subrepresentation ((polynomialRepresentation F).comp (Matrix.SpecialLinearGroup.map e))) :
    highestWeightSpan e n ≤ U ↔ X 0 ^ n ∈ U := by
  refine ⟨fun h => h (X_pow_mem_highestWeightSpan e n), fun h => ?_⟩
  change Submodule.span F _ ≤ U.toSubmodule
  apply Submodule.span_le.mpr
  rintro _ ⟨g, rfl⟩
  exact U.apply_mem_toSubmodule g h

public theorem highestWeightSpan_le_homogeneous (e : K →+* F) (n : ℕ) :
    (highestWeightSpan e n).toSubmodule ≤ homogeneousSubmodule (Fin 2) F n := by
  apply Submodule.span_le.mpr
  rintro _ ⟨g, rfl⟩
  exact (binaryForms F n).apply_mem_toSubmodule (Matrix.SpecialLinearGroup.map e g)
    (by
      change (X 0 ^ n : MvPolynomial (Fin 2) F).IsHomogeneous n
      simpa using (isHomogeneous_X F (0 : Fin 2)).pow n)

public instance highestWeightSpanFiniteDimensional (e : K →+* F) (n : ℕ) :
    FiniteDimensional F (highestWeightSpan e n).toSubmodule :=
  Module.Finite.of_injective (Submodule.inclusion (highestWeightSpan_le_homogeneous e n))
    (Submodule.inclusion_injective _)

public theorem highestWeightSpan_isIrreducible (e : K →+* F) (n : ℕ)
    (x : Fin (n + 1) → K) (hx : Function.Injective x) :
    IsIrreducible (highestWeightSpan e n).toRepresentation := by
  classical
  rw [Subrepresentation.irreducible_iff_isAtom]
  refine ⟨?_, ?_⟩
  · intro h
    have hm := X_pow_mem_highestWeightSpan e n
    rw [h] at hm
    exact (pow_ne_zero n (X_ne_zero (0 : Fin 2))) hm
  · intro U hU
    by_contra hUne
    have hUne' : U.toSubmodule ≠ ⊥ := fun h => hUne (Subrepresentation.toSubmodule_injective h)
    obtain ⟨f, hf, hf0⟩ := U.toSubmodule.ne_bot_iff.mp hUne'
    have hh : f.IsHomogeneous n := highestWeightSpan_le_homogeneous e n (hU.le hf)
    have hpure : X 0 ^ n ∈ U := by
      apply X_pow_mem_of_transvection_samples U.toSubmodule f hh hf0 (fun a => e (x a))
        (e.injective.comp hx)
      intro a
      have he : Matrix.SpecialLinearGroup.map e
          (Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one (x a)) =
          Matrix.SpecialLinearGroup.transvection zero_ne_one (e (x a)) := by
        ext l m
        simp [Matrix.SpecialLinearGroup.map_apply_coe, Matrix.SpecialLinearGroup.transvection_coe,
          Matrix.single_apply, Matrix.one_apply]
        split_ifs <;> simp
      have h := U.apply_mem_toSubmodule
        (Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one (x a)) hf
      change polynomialAction F (Matrix.SpecialLinearGroup.map e _) f ∈ U at h
      rwa [he] at h
    exact hU.not_ge ((highestWeightSpan_le_iff e n U).mpr hpure)

public theorem highestWeightSpan_isIrreducible_of_lt_card [Finite K]
    (e : K →+* F) (n : ℕ) (hn : n < Nat.card K) :
    IsIrreducible (highestWeightSpan e n).toRepresentation := by
  classical
  let : Fintype K := Fintype.ofFinite K
  obtain ⟨x⟩ := Function.Embedding.nonempty_of_card_le (α := Fin (n + 1)) (β := K)
    (by simpa only [Fintype.card_fin, Nat.card_eq_fintype_card] using Nat.succ_le_of_lt hn)
  exact highestWeightSpan_isIrreducible e n x x.injective

end Representation.SL2

