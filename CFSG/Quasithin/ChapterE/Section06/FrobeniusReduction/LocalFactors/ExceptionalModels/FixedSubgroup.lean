module

public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.ExceptionalModels.Setup


/-!
# Relative components in the induced involution's fixed subgroup

The fixed subgroup of conjugation on J is transported to J ∩ C_G(t) by
an equivalence retaining the original elements. Ordinary and C-component
membership then transfer to the subgroup of J given by the original L.
In particular this fixed subgroup is not solvable. This supplies the exact
input to intrinsic involution-centralizer calculations, without assuming
any classification of the containing group.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the
2-central involution inspection in E.6.25, printed p.256 (PDF p.267).
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.ExceptionalModels
variable {G : Type*} [Group G] {J L : Subgroup G} {t : G} {a : MulAut J}

private def fixedEquivSection
    (hf : a.fixedSubgroup = (centralizer ({t} : Set G)).subgroupOf J) :
    a.fixedSubgroup ≃* (J ⊓ centralizer ({t} : Set G) : Subgroup G) where
  toFun x := ⟨x.val, x.val.property, hf.le x.property⟩
  invFun x := ⟨⟨x.val, x.property.1⟩, by rw [hf]; exact x.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

private theorem componentMap_eq
    (hf : a.fixedSubgroup = (centralizer ({t} : Set G)).subgroupOf J) :
    (L.subgroupOf (J ⊓ centralizer ({t} : Set G))).map
        (fixedEquivSection hf).symm.toMonoidHom =
      (L.subgroupOf J).subgroupOf a.fixedSubgroup := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨fixedEquivSection hf x, hx, (fixedEquivSection hf).symm_apply_apply x⟩

/-- Transfer the actual relative C-component into the automorphism fixed group. -/
theorem cComponent_in_fixedSubgroup
    (hL : L ∈ Chapter1.cComponentsIn (J ⊓ centralizer ({t} : Set G)))
    (hf : a.fixedSubgroup = (centralizer ({t} : Set G)).subgroupOf J) :
    L.subgroupOf J ≤ a.fixedSubgroup ∧
      ((L.subgroupOf J).subgroupOf a.fixedSubgroup).IsCComponent := by
  refine ⟨?_, ?_⟩
  · rw [hf]
    intro x hx
    exact (hL.1 hx).2
  · have hm := hL.2.map_equiv (fixedEquivSection hf).symm
    rwa [componentMap_eq hf] at hm

/-- The same element-preserving transport for ordinary components. -/
theorem component_in_fixedSubgroup
    (hL : IsComponentIn L (J ⊓ centralizer ({t} : Set G)))
    (hf : a.fixedSubgroup = (centralizer ({t} : Set G)).subgroupOf J) :
    IsComponentIn (L.subgroupOf J) a.fixedSubgroup := by
  refine ⟨?_, ?_⟩
  · rw [hf]
    intro x hx
    exact (hL.1 hx).2
  · have hm := hL.2.map_equiv (fixedEquivSection hf).symm
    rwa [componentMap_eq hf] at hm

/-- The original C-component obstructs solvability of the induced fixed group. -/
theorem fixedSubgroup_not_solvable
    (hL : L ∈ Chapter1.cComponentsIn (J ⊓ centralizer ({t} : Set G)))
    (hf : a.fixedSubgroup = (centralizer ({t} : Set G)).subgroupOf J) :
    ¬ Group.IsSolvable a.fixedSubgroup := by
  intro hs
  let _ := hs
  exact (cComponent_in_fixedSubgroup hL hf).2.not_isSolvable inferInstance

end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.ExceptionalModels
