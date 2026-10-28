module
public import Theory.Representation.JankoTwo.SixDimensionalCertificate.TraceComparison
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.ConstituentDescent

/-!
# Scalar descent and the concrete Hall--Janko natural module

The two-class equivalence theorem descends from the algebraic closure to every
characteristic-two base field: coefficient projection of an extended intertwiner
is nonzero, and irreducibility makes it an equivalence. For a marked embedding,
the faithful six-dimensional natural F₄ action is absolutely irreducible by the
local geometry. The classification therefore compares any faithful degree-six
action over an F₄-algebra with this actual natural quotient and its outer twist.

The final applications discharge the character and irreducibility inputs of
`ConstituentDescent`. Coefficient Frobenius identifies the two binary twists,
and the existing involutory-extension theorem identifies the full marked outer
action. The assembly uses the constructed permutation-to-octonion embedding,
with its permitted inherited carrier-simplicity hypothesis. Its source consumer
still supplies an actual faithful six-dimensional constituent of its extended
binary action; no constituent or degree bound is inferred from a table.

Source application: Aschbacher--Smith K.4.5, printed p.460/PDF p.471, and
Hiss--Malle corrected Table 2, characteristic-two degree-six J₂ entry.
The finite certificates and the embedding retain their ATLAS attribution.
-/

@[expose] public noncomputable section

namespace Representation.JankoTwo.SixDimensionalCertificate
open Sporadic.LeechRelated.J2 LocalSpectra
open scoped _root_.TensorProduct

section Descent
universe v
variable {E : Type*} {U W : Type v} [Field E] [CharP E 2]
  [AddCommGroup U] [Module E U] [FiniteDimensional E U]
  [AddCommGroup W] [Module E W] [FiniteDimensional E W]

omit [CharP E 2] [FiniteDimensional E U] [FiniteDimensional E W] in
private theorem descend_equiv
    (ρ : Representation E Carrier U) (σ : Representation E Carrier W)
    [IsIrreducible ρ] [IsIrreducible σ]
    (e : (extendScalars (AlgebraicClosure E) ρ).Equiv
      (extendScalars (AlgebraicClosure E) σ)) : Nonempty (RepEquiv ρ σ) := by
  let C := AlgebraicClosure E
  let i : U →ₗ[E] C ⊗[E] W :=
    (e.toLinearEquiv.toLinearMap.restrictScalars E).comp (TensorProduct.mk E C U 1)
  apply ScalarConstituents.equiv_of_scalar_embedding σ ρ i
    (e.toLinearEquiv.injective.comp (Module.FaithfullyFlat.tensorProduct_mk_injective U))
  intro g u
  exact LinearMap.congr_fun (e.isIntertwining' g) ((1 : C) ⊗ₜ[E] u)

/-- The two-class completeness theorem descends to every characteristic-two base
field: equivalence over its algebraic closure yields an actual equivalence over
that base field by coefficient projection and irreducibility. -/
theorem repEquiv_or_involutionTwist
    (ρ : Representation E Carrier U) (σ : Representation E Carrier W)
    (hρ : Function.Injective ρ) (hσ : Function.Injective σ)
    (hdρ : Module.finrank E U = 6) (hdσ : Module.finrank E W = 6) :
    Nonempty (RepEquiv ρ σ) ∨
      Nonempty (RepEquiv ρ (σ.comp ExceptionalParabolics.involutionAut.toMonoidHom)) := by
  let C := AlgebraicClosure E
  let : IsAbsolutelyIrreducible ρ := isAbsolutelyIrreducible_of_faithful_six ρ hρ hdρ
  let : IsAbsolutelyIrreducible σ := isAbsolutelyIrreducible_of_faithful_six σ hσ hdσ
  let : IsIrreducible ρ := IsAbsolutelyIrreducible.irreducible_of_isAbsolutelyIrreducible ρ
  let : IsIrreducible σ := IsAbsolutelyIrreducible.irreducible_of_isAbsolutelyIrreducible σ
  have htw : Function.Injective (σ.comp ExceptionalParabolics.involutionAut.toMonoidHom) := by
    intro a b h
    exact ExceptionalParabolics.involutionAut.injective (hσ h)
  let : IsAbsolutelyIrreducible (σ.comp ExceptionalParabolics.involutionAut.toMonoidHom) :=
    isAbsolutelyIrreducible_of_faithful_six _ htw hdσ
  let : IsIrreducible (σ.comp ExceptionalParabolics.involutionAut.toMonoidHom) :=
    IsAbsolutelyIrreducible.irreducible_of_isAbsolutelyIrreducible _
  have hfρ : Function.Injective (extendScalars C ρ) := (extendScalars_faithful_iff C ρ).mp hρ
  have hfσ : Function.Injective (extendScalars C σ) := (extendScalars_faithful_iff C σ).mp hσ
  have hdρC : Module.finrank C (C ⊗[E] U) = 6 := by
    simpa only [Module.finrank_baseChange] using hdρ
  have hdσC : Module.finrank C (C ⊗[E] W) = 6 := by
    simpa only [Module.finrank_baseChange] using hdσ
  rcases equiv_or_involutionTwist (extendScalars C ρ) (extendScalars C σ)
    hfρ hfσ hdρC hdσC with he | he
  · obtain ⟨e⟩ := he
    exact Or.inl (descend_equiv ρ σ e)
  · obtain ⟨e⟩ := he
    exact Or.inr (descend_equiv ρ (σ.comp ExceptionalParabolics.involutionAut.toMonoidHom) e)
end Descent
end Representation.JankoTwo.SixDimensionalCertificate

namespace Sporadic.LeechRelated.J2.G2FourModule.MarkedEmbedding
open Representation Representation.JankoTwo.SixDimensionalCertificate
open ExceptionalParabolics Atlas.G2.Natural.BinarySemilinear
open scoped _root_.TensorProduct

/-- The six-dimensional field action is faithful on the literal carrier. -/
theorem fieldRepresentation_injective (d : MarkedEmbedding) :
    Function.Injective d.fieldRepresentation :=
  (Atlas.G2.Natural.action_injective F).comp d.inner_injective

/-- The concrete natural field action is absolutely irreducible by the local
six-line geometry, independently of any recognition statement. -/
theorem fieldRepresentation_absolutelyIrreducible (d : MarkedEmbedding) :
    IsAbsolutelyIrreducible d.fieldRepresentation :=
  LocalSpectra.isAbsolutelyIrreducible_of_faithful_six d.fieldRepresentation
    d.fieldRepresentation_injective (Atlas.G2.Natural.finrank_space F)

/-- Every extension of the marked natural field action, with any group
automorphism marking, is irreducible. -/
theorem fieldRepresentation_extendScalars_irreducible
    (d : MarkedEmbedding) (E : Type*) [Field E] [Algebra F E] (a : MulAut Carrier) :
    IsIrreducible (extendScalars E (d.fieldRepresentation.comp a.toMonoidHom)) := by
  have hf : Function.Injective (d.fieldRepresentation.comp a.toMonoidHom) := by
    intro g h he
    exact a.injective (d.fieldRepresentation_injective he)
  let : IsAbsolutelyIrreducible (d.fieldRepresentation.comp a.toMonoidHom) :=
    LocalSpectra.isAbsolutelyIrreducible_of_faithful_six _ hf (Atlas.G2.Natural.finrank_space F)
  exact IsAbsolutelyIrreducible.irreducible_of_extension _ E

universe u
/-- A faithful degree-six action over an F₄-algebra is the actual scalar
extension of the marked natural quotient, up to the specified outer twist.
This is an equivalence of representations over the given field itself. -/
theorem field_equiv_or_involutionTwist
    (d : MarkedEmbedding) {E U : Type u} [Field E] [Algebra F E]
    [AddCommGroup U] [Module E U] [FiniteDimensional E U]
    (ρ : Representation E Carrier U) (hρ : Function.Injective ρ)
    (hdρ : Module.finrank E U = 6) :
    Nonempty (RepEquiv ρ (extendScalars E d.fieldRepresentation)) ∨
      Nonempty (RepEquiv ρ
        (extendScalars E (d.fieldRepresentation.comp involutionAut.toMonoidHom))) := by
  let : CharP E 2 := charP_of_injective_algebraMap (algebraMap F E).injective 2
  exact repEquiv_or_involutionTwist ρ (extendScalars E d.fieldRepresentation)
    hρ ((extendScalars_faithful_iff E d.fieldRepresentation).mp
      d.fieldRepresentation_injective) hdρ
    (by simpa only [Module.finrank_baseChange] using Atlas.G2.Natural.finrank_space F)

/-- The two field twists have the same binary restriction, with the literal
coefficient Frobenius providing the intertwining equivalence. -/
noncomputable def innerInvolutionEquiv (d : MarkedEmbedding) :
    RepEquiv d.innerRepresentation (d.innerRepresentation.comp involutionAut.toMonoidHom) where
  toLinearEquiv := fieldEquivalence F fourFrobenius
  isIntertwining' g := LinearMap.ext (d.field_inner_action g)

/-- Actual application to constituent descent: a faithful degree-six constituent
identifies the binary irreducible action with this marked natural module.
The trace comparison and both irreducibility inputs are proved here. -/
theorem exists_binary_equiv_of_faithful_six_constituent [IsSimpleGroup Carrier]
    (d : MarkedEmbedding) {W E U : Type u}
    [AddCommGroup W] [Module (ZMod 2) W]
    [Field E] [IsAlgClosed E] [AddCommGroup U] [Module E U] [FiniteDimensional E U]
    [Algebra F E] [Algebra (ZMod 2) E] [IsScalarTower (ZMod 2) F E]
    (σ : Representation (ZMod 2) Carrier W) [IsIrreducible σ]
    (τ : Representation E Carrier U) (hτ : Function.Injective τ)
    (hdτ : Module.finrank E U = 6)
    (j : τ.IntertwiningMap (extendScalars E σ)) (hj : Function.Injective j) :
    Nonempty (RepEquiv σ d.innerRepresentation) := by
  let : CharP E 2 := charP_of_injective_algebraMap (algebraMap F E).injective 2
  let : IsIrreducible τ := LocalSpectra.isIrreducible_of_faithful_six τ hτ hdτ
  let : IsIrreducible d.innerRepresentation := d.innerRepresentation_irreducible
  have hd : Module.finrank E (E ⊗[F] V) = 6 := by
    simpa only [Module.finrank_baseChange] using Atlas.G2.Natural.finrank_space F
  have hf := (extendScalars_faithful_iff E d.fieldRepresentation).mp
    d.fieldRepresentation_injective
  rcases character_eq_or_involutionTwist τ (extendScalars E d.fieldRepresentation)
    hτ hf hdτ hd with h | h
  · let : IsIrreducible (extendScalars E (d.fieldRepresentation.comp (1 : MulAut Carrier).toMonoidHom)) :=
      d.fieldRepresentation_extendScalars_irreducible E 1
    obtain ⟨e⟩ := d.exists_equiv_of_constituent_character σ 1 τ j hj (by
      change (extendScalars E d.fieldRepresentation).character = τ.character
      exact h.symm)
    exact ⟨e⟩
  · let : IsIrreducible (extendScalars E (d.fieldRepresentation.comp involutionAut.toMonoidHom)) :=
      d.fieldRepresentation_extendScalars_irreducible E involutionAut
    obtain ⟨e⟩ := d.exists_equiv_of_constituent_character σ involutionAut τ j hj h.symm
    exact ⟨e.trans d.innerInvolutionEquiv.symm⟩

/-- The same constituent identifies the outside action on the literal extension,
including the designated field involution. -/
theorem exists_outer_equiv_of_faithful_six_constituent [IsSimpleGroup Carrier]
    (d : MarkedEmbedding) {W E U : Type u}
    [AddCommGroup W] [Module (ZMod 2) W]
    [Field E] [IsAlgClosed E] [AddCommGroup U] [Module E U] [FiniteDimensional E U]
    [Algebra F E] [Algebra (ZMod 2) E] [IsScalarTower (ZMod 2) F E]
    (σ : Representation (ZMod 2) Extension W) [IsIrreducible (σ.comp intoExtension)]
    (τ : Representation E Carrier U) (hτ : Function.Injective τ)
    (hdτ : Module.finrank E U = 6)
    (j : τ.IntertwiningMap (extendScalars E (σ.comp intoExtension)))
    (hj : Function.Injective j) :
    Nonempty (RepEquiv σ d.outerRepresentation) := by
  let : IsIrreducible d.innerRepresentation := d.innerRepresentation_irreducible
  obtain ⟨e⟩ := d.exists_binary_equiv_of_faithful_six_constituent
    (σ.comp intoExtension) τ hτ hdτ j hj
  exact d.exists_outer_equivalence σ e
end Sporadic.LeechRelated.J2.G2FourModule.MarkedEmbedding


namespace Sporadic.LeechRelated.J2.G2FourModule.Embedding
open Representation ExceptionalParabolics
open scoped TensorProduct
universe u
variable [IsSimpleGroup Carrier]

/-- Classification against the constructed, literally marked G₂(4) model.
Only inherited simplicity is used to construct the embedding; every faithful
degree-six action over the given F₄-algebra occurs in this two-element list. -/
theorem equiv_marked_of_faithful_six
    {E U : Type u} [Field E] [Algebra F E]
    [AddCommGroup U] [Module E U] [FiniteDimensional E U]
    (ρ : Representation E Carrier U) (hρ : Function.Injective ρ)
    (hdρ : Module.finrank E U = 6) :
    Nonempty (RepEquiv ρ (extendScalars E markedEmbedding.fieldRepresentation)) ∨
      Nonempty (RepEquiv ρ (extendScalars E
        (markedEmbedding.fieldRepresentation.comp involutionAut.toMonoidHom))) :=
  markedEmbedding.field_equiv_or_involutionTwist ρ hρ hdρ

/-- The constituent consumer with the marking, trace comparison and natural
irreducibility all supplied, identifying the actual binary natural restriction.
The source owner supplies its faithful six-dimensional constituent. -/
theorem binary_equiv_marked_of_faithful_six_constituent
    {W E U : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    [Field E] [IsAlgClosed E] [AddCommGroup U] [Module E U] [FiniteDimensional E U]
    [Algebra F E] [Algebra (ZMod 2) E] [IsScalarTower (ZMod 2) F E]
    (σ : Representation (ZMod 2) Carrier W) [IsIrreducible σ]
    (τ : Representation E Carrier U) (hτ : Function.Injective τ)
    (hdτ : Module.finrank E U = 6)
    (j : τ.IntertwiningMap (extendScalars E σ)) (hj : Function.Injective j) :
    Nonempty (RepEquiv σ markedEmbedding.innerRepresentation) :=
  markedEmbedding.exists_binary_equiv_of_faithful_six_constituent σ τ hτ hdτ j hj

/-- Extension recognition with the constructed marking, so the distinguished
outside involution is represented by the actual coefficient Frobenius. -/
theorem outer_equiv_marked_of_faithful_six_constituent
    {W E U : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    [Field E] [IsAlgClosed E] [AddCommGroup U] [Module E U] [FiniteDimensional E U]
    [Algebra F E] [Algebra (ZMod 2) E] [IsScalarTower (ZMod 2) F E]
    (σ : Representation (ZMod 2) Extension W) [IsIrreducible (σ.comp intoExtension)]
    (τ : Representation E Carrier U) (hτ : Function.Injective τ)
    (hdτ : Module.finrank E U = 6)
    (j : τ.IntertwiningMap (extendScalars E (σ.comp intoExtension)))
    (hj : Function.Injective j) :
    Nonempty (RepEquiv σ markedEmbedding.outerRepresentation) :=
  markedEmbedding.exists_outer_equiv_of_faithful_six_constituent σ τ hτ hdτ j hj
end Sporadic.LeechRelated.J2.G2FourModule.Embedding
