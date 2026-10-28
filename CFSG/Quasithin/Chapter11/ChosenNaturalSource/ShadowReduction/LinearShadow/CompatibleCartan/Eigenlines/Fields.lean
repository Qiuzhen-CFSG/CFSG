module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.Eigenlines.Structures
/-!
# The actual commutator is a field subspace

For a field-linear conjugation action on P, the sum of the images of
ρ(w) − 1 on a subspace U has ambient image exactly [W,U]. No bilinear
pairing is needed for this construction. When the scalars on P and V agree
on their intersection, this same group is a field subspace of V as well.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), the paragraph
after 11.3.8, printed p.775. The original-seed application is in Source.
-/

open Subgroup Representation
open scoped IsMulCommutative commutatorElement
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan
section Displacements
variable {G F : Type*} [Group G] [Field F] {P Y W : Subgroup G}
  [IsMulCommutative P] [Module F (Additive P)]

/-- Sum of displacement images under the actual linear conjugation action. -/
def commutatorFieldSpace (ρ : Representation F Y (Additive P))
    (hW : W ≤ Y) (U : Submodule F (Additive P)) : Submodule F (Additive P) :=
  ⨆ w : W, U.map (ρ ⟨w, hW w.property⟩ - LinearMap.id)

/-- The sum of displacement images is exactly the literal group commutator. -/
theorem ambient_commutatorFieldSpace (ρ : Representation F Y (Additive P))
    (hρ : ∀ (y : Y) (p : Additive P),
      ((ρ y p).toMul : G) = (MulAut.conj (y : G)) (p.toMul : G))
    (hW : W ≤ Y) (U : Submodule F (Additive P)) :
    ambientSubgroup (commutatorFieldSpace ρ hW U) = ⁅W, ambientSubgroup U⁆ := by
  have hd (w : W) (p : Additive P) :
      (((ρ ⟨w, hW w.property⟩ - (LinearMap.id : Module.End F (Additive P))) p).toMul : G) =
        ⁅(w : G), (p.toMul : G)⁆ := by
    rw [LinearMap.sub_apply, LinearMap.id_apply, sub_eq_add_neg]
    change ((ρ ⟨w, hW w.property⟩ p).toMul : G) * (p.toMul : G)⁻¹ = _
    rw [hρ]
    rfl
  apply le_antisymm
  · rintro g ⟨p, hp, rfl⟩
    change Additive.ofMul p ∈ ⨆ w : W, U.map (ρ ⟨w, hW w.property⟩ - LinearMap.id) at hp
    refine Submodule.iSup_induction (motive := fun u : Additive P => (u.toMul : G) ∈ ⁅W, ambientSubgroup U⁆) _ hp ?_ ?_ ?_
    · intro w u hu
      obtain ⟨v, hv, rfl⟩ := hu
      rw [hd]
      exact commutator_mem_commutator w.property ((mem_ambientSubgroup U v.toMul).mpr hv)
    · exact one_mem _
    · intro u v hu hv
      exact mul_mem hu hv
  · apply commutator_le.mpr
    intro w hw p hp
    obtain ⟨v, hv, rfl⟩ := hp
    have he := hd ⟨w, hw⟩ (Additive.ofMul v)
    change _ = ⁅w, P.subtype v⁆ at he
    rw [← he]
    apply (mem_ambientSubgroup _ _).mpr
    apply Submodule.mem_iSup_of_mem ⟨w, hw⟩
    exact ⟨Additive.ofMul v, hv, rfl⟩

end Displacements

section Common
variable {G F : Type*} [Group G] [Field F] {P V : Subgroup G}
  [IsMulCommutative P] [IsMulCommutative V]
  [Module F (Additive P)] [Module F (Additive V)]
variable (hcommon : ∀ (a : F) (b : Additive (P ⊓ V : Subgroup G)),
  ((a • (Subgroup.inclusion (inf_le_left : P ⊓ V ≤ P)).toAdditive b).toMul : G) =
    ((a • (Subgroup.inclusion (inf_le_right : P ⊓ V ≤ V)).toAdditive b).toMul : G))

/-- The same field subspace inside V, using agreement on the actual intersection. -/
def commonFieldSpace (U : Submodule F (Additive P)) : Submodule F (Additive V) where
  __ := ((ambientSubgroup U).subgroupOf V).toAddSubgroup
  smul_mem' a v hv := by
    let b : Additive (P ⊓ V : Subgroup G) := Additive.ofMul
      ⟨v.toMul, (map_subtype_le _ : ambientSubgroup U ≤ P) hv, v.toMul.property⟩
    have hp : (Subgroup.inclusion (inf_le_left : P ⊓ V ≤ P)).toAdditive b ∈ U :=
      (mem_ambientSubgroup U _).mp hv
    have hs := (mem_ambientSubgroup U _).mpr (U.smul_mem a hp)
    change ((a • (Subgroup.inclusion (inf_le_left : P ⊓ V ≤ P)).toAdditive b).toMul : G) ∈ ambientSubgroup U at hs
    rw [hcommon a b] at hs
    exact hs

/-- Membership is literal ambient subgroup membership. -/
theorem mem_commonFieldSpace (U : Submodule F (Additive P)) (v : Additive V) :
    v ∈ commonFieldSpace hcommon U ↔ (v.toMul : G) ∈ ambientSubgroup U := Iff.rfl

/-- Containment in V makes scalar restriction preserve the entire ambient subgroup. -/
theorem ambient_commonFieldSpace (U : Submodule F (Additive P)) (hUV : ambientSubgroup U ≤ V) :
    ambientSubgroup (commonFieldSpace hcommon U) = ambientSubgroup U := by
  apply le_antisymm
  · rintro g ⟨v, hv, rfl⟩
    exact hv
  · intro g hg
    exact ⟨⟨g, hUV hg⟩, hg, rfl⟩

end Common

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan
