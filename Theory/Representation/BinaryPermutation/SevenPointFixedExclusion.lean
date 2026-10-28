module

public import Theory.Representation.BinaryPermutation.SevenTwoGroupFixed
public import Theory.Representation.BinaryPermutation.SevenAmbientAction
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# A fixed-line two-group excludes the marked normal natural A7 action

A normal marked A7 acting on the deleted seven-letter six-space extends
to an actual S7 homomorphism with the same full action kernel. Every
two-group image fixes at least a plane. Thus a literal two-group with
one-dimensional fixed space rules out this marked normal component action.
This supplies the ordinary seven-row obstruction for the actual P-image
in the opposite Held normalizer; it assumes no ambient group model.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace BinaryPermutation.SevenAmbientAction
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

theorem no_marked_normal_core_of_fixed_line
    (ρ : Representation (ZMod 2) G V)
    (A H : Subgroup G) [H.Normal] (hA : IsPGroup 2 A)
    (hfix : Module.finrank (ZMod 2) (fixedSpace ρ A)=1)
    (e : H→*alternatingGroup (Fin 7)) (he : Function.Surjective e)
    (E : V≃ₗ[ZMod 2] core (Fin 7))
    (hE : ∀ (h : H) v, E (ρ h v)=alternatingCoreRepresentation (Fin 7) (e h) (E v)) :
    False := by
  obtain ⟨f,_,hf,_⟩ := exists_ambient_hom ρ H e he E hE
  have hb := seven_twoGroup_core_fixed_finrank (A.map f) (hA.map f)
  have hm := fixedSpace_map_equivariant ρ (coreRepresentation (Fin 7)) f E hf A
  have hd : Module.finrank (ZMod 2) (fixedSpace ρ A)=
      Module.finrank (ZMod 2) (fixedSpace (coreRepresentation (Fin 7)) (A.map f)) := by
    rw [←hm]
    exact (Submodule.equivMapOfInjective E.toLinearMap E.injective _).finrank_eq
  omega

end BinaryPermutation.SevenAmbientAction
