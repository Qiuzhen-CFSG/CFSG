module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.Saturation
public import Theory.Representation.IrreducibleScalarEmbedding
public import Theory.Representation.AbsolutelyIrreducible

/-!
# Exhaustion by a split family of modular simple representations

A family of absolutely irreducible representations over a field of prime
characteristic exhausts all simple representations once its cardinality reaches
the number of p-regular conjugacy classes. Pairwise inequivalence is checked over
the base field. The unknown representation need not be absolutely irreducible.

Extend scalars to an algebraic closure and choose a simple subrepresentation.
The modular trace-independence bound identifies it with one of the extended
candidates. Inclusion then gives an embedding of that candidate into the
extended unknown representation. Projection onto coefficients over the base
field gives a nonzero intertwiner, and Schur's lemma descends the equivalence.
A finite coordinate basis removes any universe restriction on the unknown space.

This is the standard modular simple-count argument, with descent made explicit;
it is used for the binary A₇ degree calculation underlying Aschbacher–Smith
K.1.2 and Guralnick–Malle (2002), Theorem 6.2 and Table 6.3. The class-count
bound is proved in `PRegularSimpleCount`, its saturation form in
`PSL3Three.AbsoluteDegrees.Saturation`, and coefficient descent in
`IrreducibleScalarEmbedding`. No group-specific catalogue is assumed here.
-/

public section

open scoped TensorProduct
open Representation

set_option backward.isDefEq.respectTransparency false

namespace Representation.SplitSimpleCatalogue
universe u v w

private theorem equiv_of_extended_embedding
    {F E G V W : Type*} [Field F] [Field E] [Algebra F E] [Group G]
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    (ρ : Representation F G V) [IsIrreducible ρ]
    (τ : Representation F G W) [IsIrreducible τ]
    (f : (extendScalars E τ).IntertwiningMap (extendScalars E ρ))
    (hf : Function.Injective f) : Nonempty (τ.Equiv ρ) := by
  let i : W →ₗ[F] E ⊗[F] V :=
    (f.toLinearMap.restrictScalars F).comp (TensorProduct.mk F E W 1)
  have hi : Function.Injective i :=
    hf.comp (Module.FaithfullyFlat.tensorProduct_mk_injective _)
  obtain ⟨e⟩ := ScalarConstituents.equiv_of_scalar_embedding ρ τ i hi (by
    intro g w
    change f (1 ⊗ₜ[F] τ g w) = extendScalars E ρ g (f (1 ⊗ₜ[F] w))
    simpa only [LinearMap.comp_apply, extendScalars_apply, LinearMap.baseChange_tmul,
      IntertwiningMap.toLinearMap_apply] using
      LinearMap.congr_fun (f.isIntertwining' g) (1 ⊗ₜ[F] w))
  exact ⟨e.toRepresentationEquiv⟩

private theorem exists_equiv_sameUniverse
    {F W : Type u} {G : Type v} {ι : Type w}
    [Field F] [Group G] [Finite G] [Fintype ι]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (V : ι → Type u) [∀ i, AddCommGroup (V i)] [∀ i, Module F (V i)]
    [∀ i, FiniteDimensional F (V i)] (ρ : ∀ i, Representation F G (V i))
    [∀ i, IsAbsolutelyIrreducible (ρ i)]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (hne : Pairwise fun i j => IsEmpty ((ρ i).Equiv (ρ j)))
    (hclasses : Nat.card (ConjClasses.mk '' {g : G | ¬ p ∣ orderOf g}) ≤ Nat.card ι)
    (σ : Representation F G W) [IsIrreducible σ] :
    ∃ i, Nonempty (σ.Equiv (ρ i)) := by
  let E := AlgebraicClosure F
  let : Nontrivial W := Subrepresentation.irreducible_module_nontrivial σ
  let : Nontrivial (E ⊗[F] W) :=
    (Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right F E).mpr inferInstance
  have irr (i : ι) : IsIrreducible (ρ i) :=
    IsAbsolutelyIrreducible.irreducible_of_isAbsolutelyIrreducible (ρ i)
  have irrE (i : ι) : IsIrreducible (extendScalars E (ρ i)) :=
    IsAbsolutelyIrreducible.irreducible_of_extension (ρ i) E
  have hneE : Pairwise fun i j =>
      IsEmpty ((extendScalars E (ρ i)).Equiv (extendScalars E (ρ j))) := by
    intro i j hij
    constructor
    intro e
    obtain ⟨d⟩ := equiv_of_extended_embedding (ρ j) (ρ i)
      e.toIntertwiningMap e.toLinearEquiv.injective
    exact (hne hij).false d
  obtain ⟨S, hS⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional
    (extendScalars E σ)
  let := hS
  obtain ⟨i, ⟨e⟩⟩ := exists_equiv_of_pRegular_class_bound (W := S.toSubmodule)
    (fun i => E ⊗[F] V i) (fun i => extendScalars E (ρ i)) p hneE hclasses
    S.toRepresentation
  let inc : S.toRepresentation.IntertwiningMap (extendScalars E σ) :=
    ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  obtain ⟨d⟩ := equiv_of_extended_embedding σ (ρ i)
    (inc.comp e.symm.toIntertwiningMap)
    (Subtype.val_injective.comp e.symm.toLinearEquiv.injective)
  exact ⟨i, ⟨d.symm⟩⟩

/-- A full-sized family of absolutely irreducible models over the base field
exhausts all simple modules over that field, without an absolute-simplicity
assumption on the module being classified. -/
theorem exists_equiv
    {F : Type u} {G : Type v} {ι : Type w}
    [Field F] [Group G] [Finite G] [Fintype ι]
    (V : ι → Type u) [∀ i, AddCommGroup (V i)] [∀ i, Module F (V i)]
    [∀ i, FiniteDimensional F (V i)] (ρ : ∀ i, Representation F G (V i))
    [∀ i, IsAbsolutelyIrreducible (ρ i)]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (hne : Pairwise fun i j => IsEmpty ((ρ i).Equiv (ρ j)))
    (hclasses : Nat.card (ConjClasses.mk '' {g : G | ¬ p ∣ orderOf g}) ≤ Nat.card ι)
    {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (σ : Representation F G W) [IsIrreducible σ] :
    ∃ i, Nonempty (σ.Equiv (ρ i)) := by
  classical
  let b := (Module.finBasis F W).equivFun
  let τ : Representation F G (Fin (Module.finrank F W) → F) :=
    b.conjRingEquiv.toMonoidHom.comp σ
  let e : σ.Equiv τ := Representation.Equiv.mk b (by
    intro g
    ext v
    simp [τ, LinearEquiv.conjRingEquiv])
  have hirr : τ.IsIrreducible := by
    let f := Representation.IntertwiningMap.equivLinearMapAsModule σ τ e.toIntertwiningMap
    have hf : Function.Bijective f := e.toLinearEquiv.bijective
    let ef := LinearEquiv.ofBijective f hf
    rw [irreducible_iff_isSimpleModule_asModule]
    exact ef.isSimpleModule_iff.mp ((irreducible_iff_isSimpleModule_asModule σ).mp inferInstance)
  obtain ⟨i, ⟨d⟩⟩ := exists_equiv_sameUniverse V ρ p hne hclasses τ
  exact ⟨i, ⟨e.trans d⟩⟩

end Representation.SplitSimpleCatalogue
