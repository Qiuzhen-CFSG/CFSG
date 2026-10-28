module

public import Theory.Representation.IrreducibleScalarEmbedding
public import Theory.Representation.IrreducibleTraceEquivalence
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.Perfect

/-!
# Descent of a marked Hall--Janko constituent

The marking defines the actual six-dimensional F₄ representation. Its binary
restriction is the existing twelve-dimensional action, with exactly the same
carrier homomorphism. The checked triangle relations imply determinant one.

An injective equivariant map from the extended F₄ action into an extended
binary irreducible action gives a binary equivalence by coefficient descent.
Over an algebraically closed field, equality of the constituent's trace
character produces that injective map by simple-module density. Both
constructions retain the specified automorphism of the actual carrier.

These are conditional descent results for the representation used in
Aschbacher--Smith K.4.5, printed p.460, and the F₄ degree-six entry in
Hiss--Malle, corrected Table 2 (2002). They do not assert the small-degree
classification, construct its trace certificate, or assert the existence of
a marking. Those inputs must be discharged before universal degree-twelve
recognition follows. In particular GM02 Theorem 6.6/Table 6.7 has an offender
hypothesis and is not itself that universal recognition theorem.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open Representation

namespace Sporadic.LeechRelated.J2.G2FourModule
namespace MarkedEmbedding

variable (d : MarkedEmbedding)

/-- The literal natural action over F₄, through the marked carrier map. -/
def fieldRepresentation : Representation F Carrier V :=
  (Atlas.G2.Natural.action F).comp d.inner

/-- Scalar restriction preserves every action map on the original quotient. -/
theorem innerRepresentation_apply (g : Carrier) (v : V) :
    d.innerRepresentation g v = d.fieldRepresentation g v :=
  Atlas.G2.Natural.BinarySemilinear.representation_inner F (d.inner g) v

/-- The concrete perfectness certificate puts the marked field action in SL₆. -/
theorem fieldRepresentation_det (g : Carrier) :
    LinearMap.det (d.fieldRepresentation g) = 1 := by
  let : Group.IsPerfect Carrier := carrier_isPerfect
  have h := Abelianization.commutator_subset_ker
    (LinearMap.det.comp d.fieldRepresentation).toHomUnits
    (Group.IsPerfect.mem_commutator (g := g))
  exact congrArg (fun u : Fˣ => (u : F)) h

/-- A genuine field constituent gives the binary module equivalence.
The constituent embedding, rather than its dimension, is the premise. -/
theorem exists_equiv_of_field_constituent
    {W E : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [Field E] [Algebra F E] [Algebra (ZMod 2) E] [IsScalarTower (ZMod 2) F E]
    (σ : Representation (ZMod 2) Carrier W) [IsIrreducible σ]
    [IsIrreducible d.innerRepresentation] (a : MulAut Carrier)
    (i : (extendScalars E (d.fieldRepresentation.comp a.toMonoidHom)).IntertwiningMap
      (extendScalars E σ))
    (hi : Function.Injective i) :
    Nonempty (RepEquiv σ (d.innerRepresentation.comp a.toMonoidHom)) := by
  let τ := d.innerRepresentation.comp a.toMonoidHom
  let : IsIrreducible τ :=
    (RepEquiv.irreducible_iff_group_iso (ρ := τ) (σ := d.innerRepresentation)
      a (fun _ _ => rfl)).mpr inferInstance
  let j : V →ₗ[ZMod 2] E ⊗[ZMod 2] W :=
    (i.toLinearMap.restrictScalars (ZMod 2)).comp
      ((TensorProduct.mk F E V 1).restrictScalars (ZMod 2))
  have hj : Function.Injective j :=
    hi.comp (Module.FaithfullyFlat.tensorProduct_mk_injective V)
  obtain ⟨e⟩ := ScalarConstituents.equiv_of_scalar_embedding σ τ j hj (by
    intro g v
    change i ((1 : E) ⊗ₜ[F] (d.innerRepresentation (a g) v)) =
      extendScalars E σ g (i ((1 : E) ⊗ₜ[F] v))
    rw [d.innerRepresentation_apply]
    exact LinearMap.congr_fun (i.isIntertwining' g) ((1 : E) ⊗ₜ[F] v))
  exact ⟨e.symm⟩

universe u

/-- A constituent trace calculation produces an actual binary equivalence.
Irreducibility of the extended field action remains an explicit input. -/
theorem exists_equiv_of_constituent_character
    {W E U : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    [Field E] [IsAlgClosed E] [AddCommGroup U] [Module E U]
    [FiniteDimensional E U]
    [Algebra F E] [Algebra (ZMod 2) E] [IsScalarTower (ZMod 2) F E]
    (σ : Representation (ZMod 2) Carrier W) [IsIrreducible σ]
    [IsIrreducible d.innerRepresentation] (a : MulAut Carrier)
    (τ : Representation E Carrier U) [IsIrreducible τ]
    (j : τ.IntertwiningMap (extendScalars E σ)) (hj : Function.Injective j)
    [IsIrreducible (extendScalars E (d.fieldRepresentation.comp a.toMonoidHom))]
    (htrace : (extendScalars E (d.fieldRepresentation.comp a.toMonoidHom)).character =
      τ.character) :
    Nonempty (RepEquiv σ (d.innerRepresentation.comp a.toMonoidHom)) := by
  obtain ⟨e⟩ := (character_eq_iff_equiv_of_irreducible
    (extendScalars E (d.fieldRepresentation.comp a.toMonoidHom)) τ).mp htrace
  exact d.exists_equiv_of_field_constituent σ a (j.comp e.toIntertwiningMap)
    (hj.comp e.toLinearEquiv.injective)

end MarkedEmbedding
end Sporadic.LeechRelated.J2.G2FourModule
