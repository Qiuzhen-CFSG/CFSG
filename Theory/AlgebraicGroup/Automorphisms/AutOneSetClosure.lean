module

public import Theory.AlgebraicGroup.Automorphisms.Basic

universe u

/-!
Safe closure consequences for `AutOneSet`.

The definition of `AutOneSet` allows an algebraic endomorphism to realize an
abstract automorphism either directly or after inversion.  The identity,
inverse, and the two same-orientation multiplication branches therefore need
no geometric input.  The mixed branches are recorded separately with an
explicit algebraic-group isomorphism witness; without such a witness, a
pointwise inverse of an algebraic endomorphism need not be regular in positive
characteristic.
-/

namespace Theory.AlgebraicGroup

section

variable {k : Type u} [Field k]

/-- The identity abstract automorphism is algebraically realized. -/
public lemma autOneSet_one_mem
    {K : Variety k} [AlgebraicGroup K] :
    (1 : Aut K) ∈ AutOneSet K := by
  refine Or.inl ⟨AlgebraicGroup.Morphism.id K, ?_⟩
  intro x
  rfl

/-! The inverse branch is definitional in `AutOneSet`. -/

/-- `AutOneSet` is closed under inversion. -/
public lemma autOneSet_inv_mem
    {K : Variety k} [AlgebraicGroup K]
    {σ : Aut K} (hσ : σ ∈ AutOneSet K) :
    σ⁻¹ ∈ AutOneSet K := by
  rcases hσ with ⟨f, hf⟩ | ⟨f, hf⟩
  · exact Or.inr ⟨f, hf⟩
  · exact Or.inl ⟨f, hf⟩

/-! Same-orientation multiplication branches. -/

/-- Direct algebraic realizations are closed under multiplication. -/
public lemma autOneSet_mul_mem_of_realizations
    {K : Variety k} [AlgebraicGroup K]
    {σ τ : Aut K} {f g : AlgebraicEndomorphism K}
    (hσ : IsAlgebraicRealization σ f)
    (hτ : IsAlgebraicRealization τ g) :
    σ * τ ∈ AutOneSet K := by
  refine Or.inl ⟨f.comp g, ?_⟩
  intro x
  change (σ * τ) x = f.onPoints (g.onPoints x)
  simp only [MulAut.mul_apply]
  rw [hτ, hσ]

/-!
For the symmetric branch, use `(σ * τ)⁻¹ = τ⁻¹ * σ⁻¹` and compose the
realizing morphisms in the corresponding order.
-/

/-- Symmetric algebraic realizations are closed under multiplication. -/
public lemma autOneSet_mul_mem_of_symm_realizations
    {K : Variety k} [AlgebraicGroup K]
    {σ τ : Aut K} {f g : AlgebraicEndomorphism K}
    (hσ : IsAlgebraicRealization σ.symm f)
    (hτ : IsAlgebraicRealization τ.symm g) :
    σ * τ ∈ AutOneSet K := by
  refine Or.inr ⟨g.comp f, ?_⟩
  intro x
  change (σ * τ).symm x = g.onPoints (f.onPoints x)
  change (σ * τ)⁻¹ x = g.onPoints (f.onPoints x)
  rw [mul_inv_rev]
  simp only [MulAut.mul_apply]
  have hσ' : σ⁻¹ x = f.onPoints x := by
    simpa using hσ x
  have hτ' : τ⁻¹ (f.onPoints x) = g.onPoints (f.onPoints x) := by
    simpa using hτ (f.onPoints x)
  rw [hσ', hτ']

/-!
The following mixed branches are the strongest direct replacement for the
missing algebraic-inverse construction.  They deliberately require an
explicit `AlgebraicGroup.Iso` rather than inferring regularity from pointwise
bijectivity.
-/

/-- A direct realization multiplied by a symmetric realization coming from an
explicit algebraic isomorphism remains directly realized. -/
public lemma autOneSet_mul_mem_of_realization_of_symm_realization_of_iso
    {K : Variety k} [AlgebraicGroup K]
    {σ τ : Aut K} {f : AlgebraicEndomorphism K}
    (hσ : IsAlgebraicRealization σ f)
    (e : AlgebraicGroup.Iso K K)
    (hτ : IsAlgebraicRealization τ.symm e.hom) :
    σ * τ ∈ AutOneSet K := by
  have hτ' : ∀ x, τ x = e.inv.onPoints x := by
    intro x
    apply e.toMulEquiv.injective
    change e.hom.onPoints (τ x) = e.hom.onPoints (e.inv.onPoints x)
    calc
      e.hom.onPoints (τ x) = τ.symm (τ x) := (hτ (τ x)).symm
      _ = x := by simp
      _ = e.hom.onPoints (e.inv.onPoints x) := (e.inv_hom_id x).symm
  refine Or.inl ⟨f.comp e.inv, ?_⟩
  intro x
  change (σ * τ) x = f.onPoints (e.inv.onPoints x)
  simp only [MulAut.mul_apply]
  rw [hτ' x, hσ]

/-!
The opposite mixed branch is analogous, with the inverse isomorphism on the
left.
-/

/-- A symmetric realization coming from an explicit algebraic isomorphism
multiplied by a direct realization remains directly realized. -/
public lemma autOneSet_mul_mem_of_symm_realization_of_realization_of_iso
    {K : Variety k} [AlgebraicGroup K]
    {σ τ : Aut K} {g : AlgebraicEndomorphism K}
    (e : AlgebraicGroup.Iso K K)
    (hσ : IsAlgebraicRealization σ.symm e.hom)
    (hτ : IsAlgebraicRealization τ g) :
    σ * τ ∈ AutOneSet K := by
  have hσ' : ∀ x, σ x = e.inv.onPoints x := by
    intro x
    apply e.toMulEquiv.injective
    change e.hom.onPoints (σ x) = e.hom.onPoints (e.inv.onPoints x)
    calc
      e.hom.onPoints (σ x) = σ.symm (σ x) := (hσ (σ x)).symm
      _ = x := by simp
      _ = e.hom.onPoints (e.inv.onPoints x) := (e.inv_hom_id x).symm
  refine Or.inl ⟨e.inv.comp g, ?_⟩
  intro x
  change (σ * τ) x = e.inv.onPoints (g.onPoints x)
  simp only [MulAut.mul_apply]
  rw [hτ, hσ' (g.onPoints x)]

/-- All four multiplication branches close when every realization is supplied
by an explicit algebraic-group isomorphism. -/
public lemma autOneSet_mul_mem_of_iso_realization_cases
    {K : Variety k} [AlgebraicGroup K]
    {σ τ : Aut K}
    (hσ : (∃ e : AlgebraicGroup.Iso K K,
      IsAlgebraicRealization σ e.hom) ∨
      ∃ e : AlgebraicGroup.Iso K K,
        IsAlgebraicRealization σ.symm e.hom)
    (hτ : (∃ e : AlgebraicGroup.Iso K K,
      IsAlgebraicRealization τ e.hom) ∨
      ∃ e : AlgebraicGroup.Iso K K,
        IsAlgebraicRealization τ.symm e.hom) :
    σ * τ ∈ AutOneSet K := by
  rcases hσ with ⟨eσ, hσ⟩ | ⟨eσ, hσ⟩ <;>
    rcases hτ with ⟨eτ, hτ⟩ | ⟨eτ, hτ⟩
  · refine Or.inl ⟨eσ.hom.comp eτ.hom, ?_⟩
    intro x
    change (σ * τ) x = eσ.hom.onPoints (eτ.hom.onPoints x)
    simp only [MulAut.mul_apply]
    rw [hτ, hσ]
  · exact autOneSet_mul_mem_of_realization_of_symm_realization_of_iso hσ eτ hτ
  · exact autOneSet_mul_mem_of_symm_realization_of_realization_of_iso eσ hσ hτ
  · refine Or.inr ⟨eτ.hom.comp eσ.hom, ?_⟩
    intro x
    change (σ * τ).symm x = eτ.hom.onPoints (eσ.hom.onPoints x)
    change (σ * τ)⁻¹ x = eτ.hom.onPoints (eσ.hom.onPoints x)
    rw [mul_inv_rev]
    simp only [MulAut.mul_apply]
    have hσ' : σ⁻¹ x = eσ.hom.onPoints x := by
      simpa using hσ x
    have hτ' : τ⁻¹ (eσ.hom.onPoints x) =
        eτ.hom.onPoints (eσ.hom.onPoints x) := by
      simpa using hτ (eσ.hom.onPoints x)
    rw [hσ', hτ']

end

end Theory.AlgebraicGroup
