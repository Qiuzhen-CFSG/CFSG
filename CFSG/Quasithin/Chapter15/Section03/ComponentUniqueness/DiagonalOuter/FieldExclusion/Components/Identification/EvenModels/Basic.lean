module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.SimpleSection

/-!
# The actual binary linear-three subgroup in the model inspection

The ordinary component supplied by `SimpleInput` embeds in the fixed group
and hence in the ambient simple group. Retain this literal embedding when
applying intrinsic model obstructions, and its order when excluding endpoints.
Source: Aschbacher--Smith, proof of 15.3.38, printed p.1137.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification
namespace EvenModels
open Subgroup
universe u
variable {S : Type u} [Group S] (s : SimpleInput S)

/-- Inclusion of the specified ordinary component, with its given marking. -/
def componentEmbedding : Matrix.PSL3Two.PSL →* S :=
  s.involution.fixedSubgroup.subtype.comp (s.component.subtype.comp s.equiv.symm.toMonoidHom)

theorem componentEmbedding_injective : Function.Injective (componentEmbedding s) :=
  Subtype.val_injective.comp (Subtype.val_injective.comp s.equiv.symm.injective)

include s

theorem component_card_dvd : 168 ∣ Nat.card S := by
  have h := card_dvd_of_injective (componentEmbedding s) (componentEmbedding_injective s)
  rwa [Matrix.PSL3Two.card_PSL] at h

theorem seven_dvd_card : 7 ∣ Nat.card S :=
  (by decide : 7 ∣ 168).trans (component_card_dvd s)

theorem three_dvd_card : 3 ∣ Nat.card S :=
  (by decide : 3 ∣ 168).trans (component_card_dvd s)

/-- A fixed component of the same order as the ambient finite group would
force the involutory automorphism to be the identity. -/
theorem card_ne_component [Finite S] : Nat.card S ≠ 168 := by
  intro hc
  have hsurj : Function.Surjective (componentEmbedding s) :=
    ((Nat.bijective_iff_injective_and_card _).mpr
      ⟨componentEmbedding_injective s, Matrix.PSL3Two.card_PSL.trans hc.symm⟩).surjective
  have hone : s.involution = 1 := by
    ext x
    obtain ⟨y, rfl⟩ := hsurj x
    exact (MulAut.mem_fixedSubgroup _ _).mp (s.equiv.symm y).val.property
  have ho := s.involution_order
  rw [hone, orderOf_one] at ho
  omega

end EvenModels
end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification
