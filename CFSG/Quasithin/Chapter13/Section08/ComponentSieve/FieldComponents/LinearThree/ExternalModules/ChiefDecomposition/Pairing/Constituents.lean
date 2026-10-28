module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.ChiefDecomposition.Alternatives
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.ChiefDecomposition.Sections
public import Theory.Representation.Quotient

/-!
# Noncentral irreducible component constituents

For an irreducible ambient action, the fixed space of a normal noncentral
component is zero. Thus every irreducible submodule of the restriction is
noncentral. Finite-dimensionality supplies such a submodule, and transport
along the specified component isomorphism makes the explicit H.6.1 catalogue
applicable to it. No multiplicity or pairing conclusion is assumed or proved
here.

Source: the Clifford calculation in Aschbacher–Smith 13.8.21(1), printed p.956,
using the earlier H.6.1 catalogue as an explicit input.
-/

public section

open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules
universe u
variable {H : Type*} [Group H] {V : Type u} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) H V) (K : Subgroup H) [K.Normal]
    (hirr : IsIrreducible ρ) (hmoved : ∃ k : K, ∃ v, ρ k v ≠ v)

include hirr hmoved in
/-- A simple constituent of the normal-component restriction cannot be trivial
when the ambient representation is irreducible and K acts nontrivially. -/
theorem irreducible_constituent_noncentral (A : Subrepresentation (ρ.comp K.subtype)) (hA : IsIrreducible A.toRepresentation) :
    ∃ k : K, ∃ v, A.toRepresentation k v ≠ v := by
  let : IsIrreducible ρ := hirr
  have hC : normalFixedSubrepresentation ρ K = ⊥ := by
    rcases IsSimpleOrder.eq_bot_or_eq_top (normalFixedSubrepresentation ρ K) with hb | ht
    · exact hb
    · obtain ⟨k, v, hv⟩ := hmoved
      have hvmem : v ∈ normalFixedSubrepresentation ρ K := by rw [ht]; trivial
      exact (hv (hvmem k)).elim
  by_contra! htriv
  have hA0 : A = ⊥ := by
    apply Subrepresentation.toSubmodule_injective
    apply le_bot_iff.mp
    intro v hv
    have hfixed : v ∈ normalFixedSubrepresentation ρ K := by
      intro k
      exact congrArg Subtype.val (htriv k ⟨v, hv⟩)
    rw [hC] at hfixed
    exact hfixed
  exact ((Subrepresentation.irreducible_iff_isAtom A).mp hA).ne_bot hA0


variable [FiniteDimensional (ZMod 2) V]

include hirr hmoved in
/-- An actual simple submodule of the component restriction is one of the
three models in the explicit earlier catalogue, via intertwining equivalence. -/
theorem exists_catalogued_constituent
    (eK : K ≃* BinaryLinearThree.Group)
    (hcat : LinearThreeIrreducibleCatalogue.{u}) :
    ∃ A : Subrepresentation (ρ.comp K.subtype),
      IsIrreducible A.toRepresentation ∧
      (Nonempty (Representation.Equiv (A.toRepresentation.comp eK.symm.toMonoidHom) BinaryLinearThree.W) ∨
        Nonempty (Representation.Equiv (A.toRepresentation.comp eK.symm.toMonoidHom) BinaryLinearThree.W.dual) ∨
        Nonempty (Representation.Equiv (A.toRepresentation.comp eK.symm.toMonoidHom) BinaryLinearThree.S)) := by
  let : IsIrreducible ρ := hirr
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  obtain ⟨A, hA⟩ :=
    Subrepresentation.irreducible_subrepresentation_of_finite_dimensional (ρ.comp K.subtype)
  refine ⟨A, hA, hcat.classify A.toSubmodule (A.toRepresentation.comp eK.symm.toMonoidHom) ?_ ?_⟩
  · exact (irreducible_comp_surjective_iff eK.symm.toMonoidHom
      eK.symm.surjective A.toRepresentation).mpr hA
  · obtain ⟨k, v, hv⟩ := irreducible_constituent_noncentral ρ K hirr hmoved A hA
    exact ⟨eK k, v, by simpa using hv⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules
