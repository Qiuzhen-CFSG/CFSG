module

public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.ExtensionExclusion.Relations
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.ExtensionExclusion.Reference
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.ExtensionExclusion.Certificate

/-!
# Exclusion of competing Mathieu point-restriction modules

An actual catalogue equivalence transports the full-group involution into
the extension equations. The kernel-checked finite certificates exclude every
entry other than the nonzero diagonal natural-by-dual ones. Their explicit
whole-module equivalences identify the entire restriction with the reference
module, which is then transported back to the literal point stabilizer.

The final theorems discharge the finite-exclusion premise of the earlier
conditional reductions. They require only an actual catalogue equivalence;
neither irreducibility nor semisimplicity of the restriction is assumed.
The point-restriction consumer supplies that equivalence from its faithful
irreducible full-group representation of binary dimension twelve.
Source: James (1973), Lemma 8.3, cited in Aschbacher–Smith H.12.1(1),
printed pp.393–394.
-/

public noncomputable section
namespace Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.ExtensionExclusion

open PointModel Representation.SL3FourLocalCatalogue
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel

variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
  (ρ : Representation (ZMod 2) M22TripleCover U)

/-- Return a genuine reference equivalence to the literal point stabilizer. -/
theorem point_equiv_of_transported_reference
    (e : (transportedRestriction ρ).Equiv Reference.binaryRepresentation) :
    Nonempty (Representation.Equiv (ρ.comp pointStabilizer.subtype) pointRepresentation) := by
  let f : Representation.Equiv (ρ.comp pointStabilizer.subtype)
      (Reference.binaryRepresentation.comp pointStabilizerEquiv.toMonoidHom) :=
    .mk e.toLinearEquiv (by
      intro g
      apply LinearMap.ext
      intro v
      have he := LinearMap.congr_fun (e.isIntertwining' (pointStabilizerEquiv g)) v
      change e (ρ ((pointStabilizerEquiv.symm (pointStabilizerEquiv g) : pointStabilizer) :
          M22TripleCover) v) = Reference.binaryRepresentation (pointStabilizerEquiv g) (e v) at he
      rw [pointStabilizerEquiv.symm_apply_apply] at he
      exact he)
  exact ⟨f.trans pointRepresentationEquiv.symm⟩

/-- Conditional finite-certificate assembly. The parameter exclusion premise
has no representation-theoretic conclusion and must still be proved. -/
theorem equiv_reference_of_finite_exclusion
    (hexclusion : ∀ (i : CatalogueEntry) (X : Matrix12),
      ExtensionEquations i X → ∃ p : Reference.F, p ≠ 0 ∧ i = referenceEntry p)
    (i : CatalogueEntry)
    (e : (transportedRestriction ρ).Equiv (catalogueRepresentation i)) :
    Nonempty ((transportedRestriction ρ).Equiv Reference.binaryRepresentation) := by
  obtain ⟨p, hp, hi⟩ := hexclusion i (fullMatrix ρ i e _)
    (fullMatrix_extensionEquations ρ i e)
  subst i
  exact ⟨e.trans (referenceEquivEntry p hp).symm⟩

/-- The same conditional reduction in the exact form needed by the point
restriction consumer, with the actual subgroup comparison discharged. -/
theorem point_equiv_of_finite_exclusion
    (hexclusion : ∀ (i : CatalogueEntry) (X : Matrix12),
      ExtensionEquations i X → ∃ p : Reference.F, p ≠ 0 ∧ i = referenceEntry p)
    (i : CatalogueEntry)
    (e : (transportedRestriction ρ).Equiv (catalogueRepresentation i)) :
    Nonempty (Representation.Equiv (ρ.comp pointStabilizer.subtype) pointRepresentation) := by
  obtain ⟨f⟩ := equiv_reference_of_finite_exclusion ρ hexclusion i e
  exact point_equiv_of_transported_reference ρ f

/-- A catalogue module that extends to the actual triple cover is equivalent
to the whole reference module. The full-group equations and finite exclusion
are both discharged, without any irreducibility premise on the restriction. -/
theorem equiv_reference_of_catalogue
    (i : CatalogueEntry)
    (e : (transportedRestriction ρ).Equiv (catalogueRepresentation i)) :
    Nonempty ((transportedRestriction ρ).Equiv Reference.binaryRepresentation) :=
  equiv_reference_of_finite_exclusion ρ extensionEquations_referenceEntry i e

/-- Extension exclusion in the literal point-stabilizer form used by
restriction recognition. Only the actual catalogue equivalence remains an input. -/
theorem point_equiv_of_catalogue
    (i : CatalogueEntry)
    (e : (transportedRestriction ρ).Equiv (catalogueRepresentation i)) :
    Nonempty (Representation.Equiv (ρ.comp pointStabilizer.subtype) pointRepresentation) := by
  obtain ⟨f⟩ := equiv_reference_of_catalogue ρ i e
  exact point_equiv_of_transported_reference ρ f

end Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.ExtensionExclusion
