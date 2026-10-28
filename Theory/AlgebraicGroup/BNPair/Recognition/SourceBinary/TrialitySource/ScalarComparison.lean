module
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Field.Equiv
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Group.TypeTags.Hom
public import Mathlib.RingTheory.SimpleRing.Basic

/-!
# Matching the natural and cubic tensor scalar labels

Compare the two matrix descriptions of one commutator in one common
section. Evaluation at 1, theta and fixed-field scalars forces the basis
normalizations and both scalar-twist identities on Fong--Seitz II p.219.
The reversed commutators agree because their common root line has
characteristic two. Inverting the resulting fixed-field automorphism
normalizes the leading mixed coefficient to the actual included product.

The tensor action formulas remain explicit inputs here. This comparison
neither assumes compatible labels nor constructs the source tensor module.
ScalarAlignment supplies the actual quotient maps and relabels the whole
rank-one pinning, retaining the original fixed-field inclusion.
-/


public section
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource
namespace ScalarComparison
variable {K E Z : Type*} [Field K] [Field E] [CharP E 2] [Group Z]

omit [CharP E 2] in
/-- The literal comparison of the two cubic-section coordinates on p.219.
The two descriptions need not have compatible scalar labels beforehand. -/
theorem cubic_twists (ι : K →+* E) (κ τ₁ τ₂ ρ : K ≃+* K) (θ x y : E)
    (h : ∀ a₀ a₁ a₂ b : K,
      (ι a₀+ι a₁*θ+ι a₂*θ^2)*ι (κ b) =
        x*ι (τ₂ (τ₁.symm b)) *
          (ι (τ₂ (ρ a₀))+ι (τ₂ (ρ a₁))*y+ι (τ₂ (ρ a₂))*y^2)) :
    x = 1 ∧ y = θ ∧ κ = τ₁.symm.trans τ₂ ∧ ρ.trans τ₂ = RingEquiv.refl K := by
  have hx : x = 1 := by simpa using (h 1 0 0 1).symm
  have hy : y = θ := by simpa [hx] using (h 0 1 0 1).symm
  refine ⟨hx,hy,?_,?_⟩
  · ext b
    apply ι.injective
    simpa [hx] using h 1 0 0 b
  · ext a
    apply ι.injective
    simpa [hx] using (h a 0 0 1).symm

/-- Reverse right commutators in the common section. Since their values
lie on the characteristic-two root line, inversion does not change them. -/
theorem same_section_twists (ι : K →+* E) (κ τ₁ τ₂ ρ : K ≃+* K)
    (θ x y : E) (u : Multiplicative E →* Z) (hu : Function.Injective u)
    (A : E → Z) (B : K → Z)
    (hnatural : ∀ a b, (A a)⁻¹*(B b)⁻¹*A a*B b = u (.ofAdd (a*ι (κ b))))
    (htensor : ∀ a₀ a₁ a₂ b,
      (B b)⁻¹*(A (ι a₀+ι a₁*θ+ι a₂*θ^2))⁻¹*B b*A (ι a₀+ι a₁*θ+ι a₂*θ^2) =
        u (.ofAdd (x*ι (τ₂ (τ₁.symm b)) *
          (ι (τ₂ (ρ a₀))+ι (τ₂ (ρ a₁))*y+ι (τ₂ (ρ a₂))*y^2)))) :
    x = 1 ∧ y = θ ∧ κ = τ₁.symm.trans τ₂ ∧ ρ.trans τ₂ = RingEquiv.refl K := by
  apply cubic_twists ι κ τ₁ τ₂ ρ θ x y
  intro a₀ a₁ a₂ b
  apply Multiplicative.ofAdd.injective
  apply hu
  have hr : (B b)⁻¹*(A (ι a₀+ι a₁*θ+ι a₂*θ^2))⁻¹*B b*A (ι a₀+ι a₁*θ+ι a₂*θ^2) =
      ((A (ι a₀+ι a₁*θ+ι a₂*θ^2))⁻¹*(B b)⁻¹*A (ι a₀+ι a₁*θ+ι a₂*θ^2)*B b)⁻¹ := by
    simp only [mul_inv_rev,inv_inv,mul_assoc]
  have he := htensor a₀ a₁ a₂ b
  rw [hr,hnatural,← map_inv] at he
  simpa only [← ofAdd_neg, CharTwo.neg_eq] using he

/-- The common-section comparison determines the automorphism used to
relabel the whole fixed-field actor. After that change its leading mixed
coefficient is ordinary multiplication by the actual included scalar. -/
theorem normalized_section (ι : K →+* E) (κ τ₁ τ₂ ρ : K ≃+* K)
    (θ x y : E) (u : Multiplicative E →* Z) (hu : Function.Injective u)
    (A : E → Z) (B : K → Z)
    (hnatural : ∀ a b, (A a)⁻¹*(B b)⁻¹*A a*B b = u (.ofAdd (a*ι (κ b))))
    (htensor : ∀ a₀ a₁ a₂ b,
      (B b)⁻¹*(A (ι a₀+ι a₁*θ+ι a₂*θ^2))⁻¹*B b*A (ι a₀+ι a₁*θ+ι a₂*θ^2) =
        u (.ofAdd (x*ι (τ₂ (τ₁.symm b)) *
          (ι (τ₂ (ρ a₀))+ι (τ₂ (ρ a₁))*y+ι (τ₂ (ρ a₂))*y^2)))) :
    x = 1 ∧ y = θ ∧ κ = τ₁.symm.trans τ₂ ∧ ρ.trans τ₂ = RingEquiv.refl K ∧
      ∀ a b, (B ((τ₁.symm.trans τ₂).symm b))⁻¹*(A a)⁻¹*
        B ((τ₁.symm.trans τ₂).symm b)*A a = u (.ofAdd (a*ι b)) := by
  obtain ⟨hx,hy,hκ,hρ⟩ := same_section_twists ι κ τ₁ τ₂ ρ θ x y u hu A B hnatural htensor
  refine ⟨hx,hy,hκ,hρ,?_⟩
  intro a b
  have he := hnatural a ((τ₁.symm.trans τ₂).symm b)
  rw [hκ,RingEquiv.apply_symm_apply] at he
  have hi := congrArg Inv.inv he
  simpa only [mul_inv_rev,inv_inv,mul_assoc,← map_inv,
    ← ofAdd_neg,CharTwo.neg_eq] using hi

end ScalarComparison
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource
