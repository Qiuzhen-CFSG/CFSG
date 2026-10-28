module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.SectionTransport

/-!
# Point stabilizers and their intrinsic two-cores

The point in the last three paragraphs of 15.3.49 is a vector, not an
arbitrary subgroup of the actor. Equivariant coordinates carry its stabilizer
to the stabilizer of the corresponding model vector, and carry the intrinsic
two-core along with it. A strong offender in that core therefore contradicts
a bound proved at the identified model point.

The application below starts with the published conjugation action on the
literal section `U_H/Z` and keeps the star conjugacy of the two offenders.
Module coordinates and the model bound are separate inputs; no model
exclusion is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed p.1145.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative

section Transport

variable {K D V W : Type*} [Group K] [Group D]
  [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- The pointwise stabilizer of the indicated vector. -/
def pointStabilizer (ρ : Representation (ZMod 2) K V) (z : V) : Subgroup K where
  carrier := {g | ρ g z = z}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change ρ a z = z at ha
    change ρ b z = z at hb
    change ρ (a * b) z = z
    simpa only [map_mul, Module.End.mul_apply, hb] using ha
  inv_mem' := by
    intro a ha
    change ρ a z = z at ha
    change ρ a⁻¹ z = z
    have h := congrArg (fun v => ρ a⁻¹ v) ha
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] using h.symm

theorem localTwoCore_le (P : Subgroup K) : localTwoCore P ≤ P := by
  rintro x ⟨y, _, rfl⟩
  exact y.property

/-- Taking the intrinsic two-core commutes with an actual change of actors. -/
theorem localTwoCore_map_equiv (e : K ≃* D) (P : Subgroup K) :
    (localTwoCore P).map e.toMonoidHom = localTwoCore (P.map e.toMonoidHom) := by
  let f : P ≃* P.map e.toMonoidHom := e.subgroupMap P
  have h := pCore_map_iso 2 f
  have hc : e.toMonoidHom.comp P.subtype =
      (P.map e.toMonoidHom).subtype.comp f.toMonoidHom := rfl
  change ((pCore 2 P).map P.subtype).map e.toMonoidHom = _
  rw [map_map, hc, ← map_map, h]
  rfl

/-- Stabilizers are transported using the action on the point itself. -/
theorem pointStabilizer_map_equivariant
    (ρ : Representation (ZMod 2) K V) (σ : Representation (ZMod 2) D W)
    (e : K ≃* D) (E : V ≃ₗ[ZMod 2] W)
    (hE : ∀ g v, E (ρ g v) = σ (e g) (E v)) (z : V) :
    (pointStabilizer ρ z).map e.toMonoidHom = pointStabilizer σ (E z) := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    change ρ g z = z at hg
    change σ (e g) (E z) = E z
    rw [← hE, hg]
  · intro hx
    obtain ⟨g, rfl⟩ := e.surjective x
    refine ⟨g, ?_, rfl⟩
    apply E.injective
    rw [hE]
    exact hx

/-- A model point-core calculation, applied after both identifications. -/
theorem exclude_strong_at_identified_point
    (ρ : Representation (ZMod 2) K V) (σ : Representation (ZMod 2) D W)
    (e : K ≃* D) (E : V ≃ₗ[ZMod 2] W)
    (hE : ∀ g v, E (ρ g v) = σ (e g) (E v))
    (z : V) (P A : Subgroup K) (hP : P = pointStabilizer ρ z)
    (hAP : A ≤ localTwoCore P)
    (hmodel : ∀ B ≤ localTwoCore (pointStabilizer σ (E z)),
      ¬ IsStrongOffender σ B)
    (hA : IsStrongOffender ρ A) : False := by
  have hmap : A.map e.toMonoidHom ≤ localTwoCore (pointStabilizer σ (E z)) := by
    have h := map_mono (f := e.toMonoidHom) hAP
    rw [localTwoCore_map_equiv, hP, pointStabilizer_map_equivariant ρ σ e E hE] at h
    exact h
  exact hmodel _ hmap (strong_map_equivariant ρ σ e.toMonoidHom e.injective E hE hA)

/-- The point may lie in the component submodule `Ũ₀`. Its stabilizer is
still taken in the whole actor, and the original offender remains strong
after restriction to that submodule. -/
theorem exclude_strong_at_submodule_point [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) K V) (σ : Representation (ZMod 2) D W)
    (U₀ : Subrepresentation ρ) (e : K ≃* D)
    (E : U₀.toSubmodule ≃ₗ[ZMod 2] W)
    (hE : ∀ g v, E (U₀.toRepresentation g v) = σ (e g) (E v))
    (z : U₀.toSubmodule) (P A : Subgroup K)
    (hP : P = pointStabilizer U₀.toRepresentation z)
    (hAP : A ≤ localTwoCore P)
    (hmodel : ∀ B ≤ localTwoCore (pointStabilizer σ (E z)),
      ¬ IsStrongOffender σ B)
    (hA : IsStrongOffender ρ A) : False := by
  apply exclude_strong_at_identified_point U₀.toRepresentation σ e E hE z P A
    hP hAP hmodel
  exact ⟨hA.1, (fixedCodim_subrepresentation_le ρ U₀ A).trans_lt hA.2⟩

end Transport

section ActualSection

variable {G : Type*} [Group G] [Finite G]
  {H U Z Vα Vγ : Subgroup G} [IsElementaryAbelian 2 U]

/-- The source application, retaining `Y₀* T*`, its point, and the actual
conjugation representation and star conjugacy. -/
theorem exclude_star_at_identified_point
    (action : SectionAction H U Z) (Y₀ T : Subgroup G)
    {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) D W)
    (e : (H ⧸ pCore 2 H) ≃* D)
    (E : Additive (U ⧸ Z.subgroupOf U) ≃ₗ[ZMod 2] W)
    (hE : ∀ g v, E (action.representation g v) = σ (e g) (E v))
    (z : Additive (U ⧸ Z.subgroupOf U))
    (hP : starImage H Y₀ ⊔ starImage H T = pointStabilizer action.representation z)
    (hα : starImage H Vα ≤ localTwoCore (starImage H Y₀ ⊔ starImage H T))
    (g : H ⧸ pCore 2 H)
    (hconj : starImage H Vα = (starImage H Vγ).map (MulAut.conj g).toMonoidHom)
    (hmodel : ∀ B ≤ localTwoCore (pointStabilizer σ (E z)),
      ¬ IsStrongOffender σ B)
    (hγ : IsStrongOffender action.representation (starImage H Vγ)) : False :=
  exclude_strong_at_identified_point action.representation σ e E hE z _ _ hP hα
    hmodel (strong_alpha action hγ g hconj)

end ActualSection

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions
