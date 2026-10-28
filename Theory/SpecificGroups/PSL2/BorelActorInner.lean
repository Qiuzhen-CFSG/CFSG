module
public import Theory.GroupAction.BorelActorInner
public import Theory.SpecificGroups.SL2.NormalSylowFieldAction
public import Theory.SpecificGroups.PSL2.BorelCoprimeFieldAction
public import Theory.GroupTheory.AutomorphismOvergroupCore

/-!
# Borel-normalized actors on binary PSL₂

Pull the inner intersection back through the faithful inner action. Its
intersection with a Sylow normalizer is a 2-group lying in the Sylow
subgroup. Normalization of the actor subgroup puts every Borel displacement
in that intersection. The root and torus calculation then kills the field
part of each actor. The marked Sylow subgroup is arbitrary.

Source: the outer-action comparison in Aschbacher--Smith 14.6.15, p.1035.
-/

public section
open Subgroup
open scoped MatrixGroups
open Atlas.RankOneFieldAutomorphisms
open Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.Semilinear
namespace Theory.PSL2

theorem borelActorInner (F : Type*) [Field F] [Finite F] [CharP F 2]
    (P : Sylow 2 PSL(2,F)) (A : Subgroup (MulAut PSL(2,F)))
    (hP : ∀ α ∈ A, (P : Subgroup PSL(2,F)).map α.toMonoidHom = P)
    (hB : (normalizer (P : Set PSL(2,F))).map MulAut.conj ≤ normalizer (A : Set _))
    (hi : IsPGroup 2 (A ⊓ MulAut.innerSubgroup PSL(2,F) : Subgroup _)) :
    A ≤ MulAut.innerSubgroup PSL(2,F) := by
  let D := (A ⊓ MulAut.innerSubgroup PSL(2,F)).comap MulAut.conj
  have hinj : Function.Injective (MulAut.conj : PSL(2,F) →* _) :=
    Theory.GroupTheory.conj_injective_of_center_eq_bot (psl_center_eq_bot (F := F))
  have hD : IsPGroup 2 D := hi.comap_of_injective _ hinj
  intro α hα
  obtain ⟨g,σ,he⟩ := exists_inner_field F α
  have hd (x : PSL(2,F)) (hx : x ∈ normalizer (P : Set PSL(2,F))) :
      x⁻¹ * α x ∈ (P : Subgroup PSL(2,F)) := by
    have hb := hB (mem_map_of_mem MulAut.conj hx)
    have ha : (MulAut.conj x)⁻¹ * α * MulAut.conj x ∈ A :=
      (mem_normalizer_iff.mp (inv_mem hb) α).mp hα
    have heq : MulAut.conj (x⁻¹ * α x) =
        ((MulAut.conj x)⁻¹ * α * MulAut.conj x) * α⁻¹ := by
      ext y
      change (x⁻¹ * α x) * y * (x⁻¹ * α x)⁻¹ =
        x⁻¹ * α (x * α.symm y * x⁻¹) * x
      simp only [map_mul,map_inv,MulEquiv.apply_symm_apply]
      group
    have hm : x⁻¹ * α x ∈ D :=
      ⟨heq ▸ A.mul_mem ha (A.inv_mem hα), ⟨x⁻¹ * α x,rfl⟩⟩
    have hxα : α x ∈ normalizer (P : Set PSL(2,F)) := by
      have hh := mem_map_of_mem α.toMonoidHom hx
      have heN : (normalizer (P : Set PSL(2,F))).map α.toMonoidHom =
          normalizer (P : Set PSL(2,F)) := by
        calc
          _ = normalizer ((P : Subgroup PSL(2,F)).map α.toMonoidHom : Set _) :=
            map_normalizer_eq_of_bijective _ α.bijective
          _ = _ := congrArg (fun D : Subgroup PSL(2,F) => normalizer (D : Set PSL(2,F))) (hP α hα)
      exact heN ▸ hh
    have hh : x⁻¹ * α x ∈ D ⊓ normalizer (P : Set PSL(2,F)) :=
      ⟨hm,(normalizer (P : Set PSL(2,F))).mul_mem
        ((normalizer (P : Set PSL(2,F))).inv_mem hx) hxα⟩
    rw [hD.inf_normalizer_sylow P] at hh
    exact hh.2
  have hσ : σ = 1 := NormalSylow.field_eq_one_of_normalizer_displacements F P g σ
    (he ▸ hP α hα) (fun x hx => he ▸ hd x hx)
  rw [he,hσ]
  have hf : Atlas.fieldEquivPSL 2 (1 : F ≃+* F) = 1 :=
    (pslFieldAction (F := F)).map_one
  rw [hf,mul_one]
  exact ⟨g,rfl⟩

/-- The detector holds on any group with the specified binary PSL₂ model. -/
theorem borelActorInner_of_mulEquiv {C : Type*} [Group C] [Finite C]
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    (e : C ≃* PSL(2,F)) : MulAut.BorelActorInner C :=
  (show MulAut.BorelActorInner PSL(2,F) from borelActorInner F).of_mulEquiv e

end Theory.PSL2
