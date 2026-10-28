module

public import Theory.Representation.QuadraticFourGroup.TensorClassification.NaturalAction

/-!
# External tensors and their coefficient fields

The two factors act on separate tensor coordinates over a common field.
Equivariant isomorphisms of the factors induce an actual tensor isomorphism.
The trace of an external tensor is the product of its two traces; for the
explicit Frobenius natural modules, these traces range over the entire
embedded matrix field. This identifies the field that must be recovered in
the finite-field descent in GLS2, Theorem 25.14, Step 5 and its remarks.
-/

@[expose] public section

open scoped TensorProduct
namespace Representation.QuadraticFourGroup.TensorClassification

/-- External tensor product over the coefficient field. -/
noncomputable def externalTensor {k G H U W : Type*} [Field k] [Monoid G] [Monoid H]
    [AddCommGroup U] [Module k U] [AddCommGroup W] [Module k W]
    (ρ : Representation k G U) (σ : Representation k H W) :
    Representation k (G × H) (U ⊗[k] W) :=
  Representation.tprod (ρ.comp (MonoidHom.fst G H)) (σ.comp (MonoidHom.snd G H))

theorem externalTensor_apply {k G H U W : Type*} [Field k] [Monoid G] [Monoid H]
    [AddCommGroup U] [Module k U] [AddCommGroup W] [Module k W]
    (ρ : Representation k G U) (σ : Representation k H W) (g : G × H) :
    externalTensor ρ σ g = TensorProduct.map (ρ g.1) (σ g.2) := rfl

theorem externalTensor_character {k G H U W : Type*} [Field k] [Monoid G] [Monoid H]
    [AddCommGroup U] [Module k U] [FiniteDimensional k U]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (ρ : Representation k G U) (σ : Representation k H W) (g : G × H) :
    (externalTensor ρ σ).character g = ρ.character g.1 * σ.character g.2 :=
  LinearMap.trace_tensorProduct' (ρ g.1) (σ g.2)

/-- Tensoring two genuine equivariant linear equivalences. -/
noncomputable def externalTensorEquiv {k G H U U' W W' : Type*}
    [Field k] [Monoid G] [Monoid H]
    [AddCommGroup U] [Module k U] [AddCommGroup U'] [Module k U']
    [AddCommGroup W] [Module k W] [AddCommGroup W'] [Module k W']
    {ρ : Representation k G U} {ρ' : Representation k G U'}
    {σ : Representation k H W} {σ' : Representation k H W'}
    (e : ρ.Equiv ρ') (f : σ.Equiv σ') :
    (externalTensor ρ σ).Equiv (externalTensor ρ' σ') :=
  .mk (TensorProduct.congr e.toLinearEquiv f.toLinearEquiv) (by
    intro g
    ext u w
    change e (ρ g.1 u) ⊗ₜ[k] f (σ g.2 w) = ρ' g.1 (e u) ⊗ₜ[k] σ' g.2 (f w)
    exact congrArg₂ (fun u' w' => u' ⊗ₜ[k] w')
          (Representation.IntertwiningMap.isIntertwining ρ ρ' e.toIntertwiningMap g.1 u)
          (Representation.IntertwiningMap.isIntertwining σ σ' f.toIntertwiningMap g.2 w))

/-- The full tensor trace field, even when the Frobenius twists differ. -/
theorem mappedFrobeniusTensor_character_range {n : ℕ} {F : Type*} [Field F]
    (e : GaloisField 2 n →+* F) (i j : ℕ) :
    Set.range (externalTensor (mappedFrobeniusNatural e i)
      (mappedFrobeniusNatural e j)).character = Set.range e := by
  apply Set.Subset.antisymm
  · rintro _ ⟨g, rfl⟩
    have h₁ : (mappedFrobeniusNatural e i).character g.1 ∈ Set.range e := by
      rw [← mappedFrobeniusNatural_character_range e i]
      exact ⟨_, rfl⟩
    have h₂ : (mappedFrobeniusNatural e j).character g.2 ∈ Set.range e := by
      rw [← mappedFrobeniusNatural_character_range e j]
      exact ⟨_, rfl⟩
    obtain ⟨a, ha⟩ := h₁
    obtain ⟨b, hb⟩ := h₂
    exact ⟨a*b, by rw [externalTensor_character, map_mul, ha, hb]⟩
  · rintro _ ⟨a, rfl⟩
    have h₁ : e a ∈ Set.range (mappedFrobeniusNatural e i).character := by
      rw [mappedFrobeniusNatural_character_range]
      exact ⟨a, rfl⟩
    have h₂ : e 1 ∈ Set.range (mappedFrobeniusNatural e j).character := by
      rw [mappedFrobeniusNatural_character_range]
      exact ⟨1, rfl⟩
    obtain ⟨g, hg⟩ := h₁
    obtain ⟨h, hh⟩ := h₂
    exact ⟨(g,h), by rw [externalTensor_character, hg, hh, map_one, mul_one]⟩

end Representation.QuadraticFourGroup.TensorClassification

end
