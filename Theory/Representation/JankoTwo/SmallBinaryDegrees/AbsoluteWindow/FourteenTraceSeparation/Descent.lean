module

public import Theory.Representation.FrobeniusFixedDescent

/-!
# Faithful absolutely irreducible descent from binary traces

Over a finite field of characteristic two, binary traces identify an absolutely
irreducible representation with its Frobenius twist after scalar extension.
Frobenius descent gives a model over F₂ in the same dimension. The actual
intertwiner preserves faithfulness. Density after scalar extension proves that
the descended model is still absolutely irreducible, not merely irreducible.

The consumer in `FourteenTraceSeparation` reduces the degree-fourteen Hall--Janko
trace problem to exclusion of a faithful absolutely irreducible binary model.
This descent does not establish that exclusion.

Source application: Guralnick--Malle, Classification of 2F-modules I,
Proposition 5.1, manuscript p.16; the field-of-definition clause for degree 14
in the corrected Hiss--Malle Table 2.
-/

public section
open scoped TensorProduct
namespace Representation

set_option backward.isDefEq.respectTransparency false in
private theorem absolute_of_extension {F C G V : Type*}
    [Field F] [Field C] [Algebra F C] [IsAlgClosed C]
    [Monoid G] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (σ : Representation F G V) [IsIrreducible (extendScalars C σ)] :
    IsAbsolutelyIrreducible σ := by
  let : IsIrreducible σ := irreducible_of_extendScalars C σ
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial σ
  constructor
  apply irreducible_of_jacobson_density_surjective
  rw [← extendScalars_surj_iff, extendScalars_surj_iff C σ]
  exact jacobson_density_surjective_isAlgClosed_rep (extendScalars C σ)

/-- Binary traces give an actual faithful absolutely irreducible binary model
of the same dimension. The acting monoid need not be finite. -/
theorem exists_faithful_absolute_binary_model_of_binary_traces {K U G : Type*} [Field K] [Finite K] [CharP K 2]
    [Monoid G] [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (τ : Representation K G U) (hf : Function.Injective τ)
    (hi : τ.IsAbsolutelyIrreducible) (htrace : ∀ g, τ.character g ^ 2 = τ.character g) :
    ∃ σ : Representation (ZMod 2) G (Fin (Module.finrank K U) → ZMod 2),
      Function.Injective σ ∧ σ.IsAbsolutelyIrreducible := by
  classical
  let C := AlgebraicClosure K
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  let : Module.Finite (ZMod 2) K := Module.Finite.of_finite
  let : Algebra.IsAlgebraic (ZMod 2) C := Algebra.IsAlgebraic.trans (ZMod 2) K C
  let ρ := extendScalars C τ
  let : IsIrreducible ρ := hi.irreducible_of_closure
  let : IsIrreducible (frobeniusConjugate 2 1 ρ) := frobeniusConjugate_isIrreducible 2 1 ρ
  have hchar : ρ.character = (frobeniusConjugate 2 1 ρ).character := by
    funext g
    rw [character_frobeniusConjugate]
    change LinearMap.trace C _ ((τ g).baseChange C) =
      LinearMap.trace C _ ((τ g).baseChange C) ^ (2 ^ 1)
    rw [LinearMap.trace_baseChange, pow_one, ← map_pow]
    exact congrArg (algebraMap K C) (htrace g).symm
  have hequiv := (character_eq_iff_equiv_of_irreducible ρ
    (frobeniusConjugate 2 1 ρ)).mp hchar
  let b : Module.Basis (Fin (Module.finrank K U)) C (C ⊗[K] U) :=
    (Module.finBasis C (C ⊗[K] U)).reindex (finCongr Module.finrank_baseChange)
  obtain ⟨σ, ⟨e⟩⟩ := exists_primeField_model_of_frobenius_equiv 2 ρ b hequiv
  have hfρ : Function.Injective ρ := (extendScalars_faithful_iff C τ).mp hf
  have hfσ : Function.Injective σ := by
    intro g h hgh
    apply hfρ
    have he : mapCoefficients (algebraMap (ZMod 2) C) σ g =
        mapCoefficients (algebraMap (ZMod 2) C) σ h := by
      apply LinearMap.toMatrix'.injective
      simp only [mapCoefficients_toMatrix, hgh]
    simpa only [e.conj_apply_self] using congrArg e.conj he
  let er : mapCoefficients (algebraMap (ZMod 2) C) σ ≃ₗ ρ :=
    { toLinearEquiv := e.toLinearEquiv
      isIntertwining' := e.isIntertwining' }
  let : IsIrreducible (extendScalars C σ) :=
    (extendScalarsMapCoefficientsEquiv (E := C) σ).irreducible_of_euqiv
      (er.irreducible_of_euqiv inferInstance)
  exact ⟨σ, hfσ, absolute_of_extension (C := C) σ⟩

end Representation
