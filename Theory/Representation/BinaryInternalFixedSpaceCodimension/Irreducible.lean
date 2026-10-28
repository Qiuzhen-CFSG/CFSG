module

public import Theory.Representation.BinaryInternalFixedSpaceCodimension.Action
public import Theory.Representation.BinaryConjugationSection.Irreducible
public import Theory.Representation.BinaryOffender.QuasisimpleImage

/-!
# Irreducibility of the literal internal action

A subgroup minimal under the given normalizer action supplies the original
binary conjugation section with trivial denominator. Both the original
representation and its faithful image are irreducible.
-/

namespace Representation.BinaryInternalFixedSpaceCodimension
open Subgroup BinaryOffender
open scoped IsMulCommutative
variable {G : Type*} [Group G]

public theorem irreducible_of_subgroup_minimal
    (W I : Subgroup G) [IsElementaryAbelian 2 W]
    (hWI : W≤I) (hI : I≤normalizer (W : Set G)) (hne : W≠⊥)
    (hmin : ∀ A : Subgroup G, A≤W → I≤normalizer (A : Set G) → A=⊥ ∨ A=W) :
    (representation W I hI).IsIrreducible ∧
      (imageRepresentation (representation W I hI)).IsIrreducible := by
  let : Nontrivial W := (nontrivial_iff_ne_bot W).mpr hne
  let d : BinaryConjugationSection I W ⊥ (representation W I hI) := {
    section_le := hWI
    kernel_le := bot_le
    normalized := hI
    coordinates := {
      toFun := fun w => Multiplicative.ofAdd (Additive.ofMul w)
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
    onto := fun w => ⟨w.toAdd.toMul,rfl⟩
    kernel_eq := by
      ext w
      change w=1 ↔ (w:G)=1
      exact Subtype.val_inj.symm
    equivariant := fun _ _ => rfl }
  have hi := d.irreducible_of_subgroup_minimal (by
    intro A hAW hIA
    rcases hmin A hAW hIA with hb | ht
    · exact Or.inr hb.le
    · exact Or.inl ht)
  exact ⟨hi,imageRepresentation_irreducible _ hi⟩

end Representation.BinaryInternalFixedSpaceCodimension
