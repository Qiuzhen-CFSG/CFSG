module
public import Theory.Representation.PSL3Two.NaturalPlaneStabilizer.Pointwise
public import Theory.Representation.BinaryFullLinearRecognition
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Common-axis groups in natural binary degree three

The pointwise fixer of a plane is the two-core of its stabilizer and has
order four. A faithful four-group with displacement one is therefore that
entire fixer. Coordinate conjugation marks the action of the original group,
including the actual subgroup image; no abstract four-group is substituted.

Source application: Aschbacher--Smith 13.1.9, printed p.871, the common-axis
transvection group after identification of both natural tensor factors.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace BinaryLinearThree.NaturalPlaneStabilizer
open Matrix.PSL3Two

theorem core_card (B : Submodule (ZMod 2) Vector)
    (hB : Module.finrank (ZMod 2) B = 2) : Nat.card ((stabilizer B).pCoreIn 2) = 4 := by
  obtain ⟨g,hg⟩ := exists_stabilizer_eq B hB
  rw [hg,← map_pCoreIn_of_injective 2 lineParabolicSL
    (MulAut.conj g).toMonoidHom (MulAut.conj g).injective,
    lineParabolicSL_pCoreIn_two_eq_R]
  rw [← Nat.card_congr (R.equivMapOfInjective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).toEquiv]
  exact card_R

theorem eq_core_of_card_four (A : Subgroup Group) (hc : Nat.card A = 4)
    (hd : fixedCodim W A = 1) :
    A = (stabilizer (fixedSpace W A)).pCoreIn 2 := by
  have hdim := fixedCodim_add_finrank W A
  have hplane : Module.finrank (ZMod 2) (fixedSpace W A) = 2 := by
    have hv : Module.finrank (ZMod 2) Vector = 3 := by simp [Vector]
    rw [hd,hv] at hdim
    omega
  apply eq_of_le_of_card_ge
  · intro a ha
    rw [mem_core_iff_fixes _ hplane]
    exact fun v hv => hv ⟨a,ha⟩
  · rw [core_card _ hplane,hc]
end BinaryLinearThree.NaturalPlaneStabilizer

namespace Representation.BinaryThreeCoordinates
variable {H V : Type*} [Group H] [AddCommGroup V] [Module (ZMod 2) V]

noncomputable def matrixAction (σ : Representation (ZMod 2) H V)
    (f : V ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) : H →* SL(3,ZMod 2) :=
  (((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin 3 → ZMod 2)).trans
    (BinaryLinear.OuterCyclic.slEquivLinear 3).symm).toMonoidHom.comp
      ((LinearMap.GeneralLinearGroup.congrLinearEquiv f).toMonoidHom.comp σ.asGroupHom))

theorem matrixAction_apply (σ : Representation (ZMod 2) H V)
    (f : V ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) (g : H) (v : V) :
    f (σ g v) = (matrixAction σ f g).val.mulVec (f v) := by
  have h := BinaryLinear.OuterCyclic.slEquivLinear_apply 3 (matrixAction σ f g) (f v)
  rw [show BinaryLinear.OuterCyclic.slEquivLinear 3 (matrixAction σ f g) =
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin 3 → ZMod 2))
      ((LinearMap.GeneralLinearGroup.congrLinearEquiv f) (σ.asGroupHom g)) from
        (BinaryLinear.OuterCyclic.slEquivLinear 3).apply_symm_apply _] at h
  simpa [Representation.asGroupHom_apply] using h

theorem matrixAction_injective_on (σ : Representation (ZMod 2) H V)
    (f : V ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) (A : Subgroup H)
    (hf : ∀ a ∈ A, (∀ v, σ a v = v) → a = 1) :
    Function.Injective ((matrixAction σ f).comp A.subtype) := by
  apply (injective_iff_map_eq_one _).mpr
  intro a ha
  apply Subtype.ext
  apply hf a a.property
  intro v
  apply f.injective
  rw [matrixAction_apply]
  change matrixAction σ f a = 1 at ha
  rw [ha]
  simp

theorem matrixAction_fixed_plane [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) H V)
    (f : V ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) (A : Subgroup H)
    (hd : fixedCodim σ A = 1) :
    Module.finrank (ZMod 2)
      (fixedSpace BinaryLinearThree.W (A.map (matrixAction σ f))) = 2 := by
  have he := fixedCodim_map_equivariant σ BinaryLinearThree.W (matrixAction σ f) f
    (matrixAction_apply σ f) A
  have hh := fixedCodim_add_finrank BinaryLinearThree.W (A.map (matrixAction σ f))
  have hv : Module.finrank (ZMod 2) BinaryLinearThree.Vector = 3 := by
    simp [BinaryLinearThree.Vector]
  rw [←he,hd,hv] at hh
  omega

theorem matrixAction_actor_eq_core [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) H V)
    (f : V ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) (A : Subgroup H)
    (hf : ∀ a ∈ A, (∀ v, σ a v = v) → a = 1)
    (hc : Nat.card A = 4) (hd : fixedCodim σ A = 1) :
    A.map (matrixAction σ f) =
      (BinaryLinearThree.NaturalPlaneStabilizer.stabilizer
        (fixedSpace BinaryLinearThree.W (A.map (matrixAction σ f)))).pCoreIn 2 := by
  let φ := matrixAction σ f
  have hi := matrixAction_injective_on σ f A hf
  have hcard : Nat.card (A.map φ) = 4 := by
    have hrange : (φ.comp A.subtype).range = A.map φ := by
      rw [MonoidHom.range_comp,range_subtype]
    rw [←hrange,←Nat.card_congr (MonoidHom.ofInjective hi).toEquiv]
    exact hc
  have heq := fixedCodim_map_equivariant σ BinaryLinearThree.W φ f
    (matrixAction_apply σ f) A
  exact BinaryLinearThree.NaturalPlaneStabilizer.eq_core_of_card_four _ hcard
    (heq.symm.trans hd)
end Representation.BinaryThreeCoordinates
