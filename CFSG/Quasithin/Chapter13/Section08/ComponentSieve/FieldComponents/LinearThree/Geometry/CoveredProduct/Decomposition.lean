module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Definitions
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# A compatible product map from the actual component centralizer

If H* acts on its centerless L₃(2) component by inner automorphisms,
then H* is the product of that component and its actual centralizer.
Multiplication gives an equivalence whose inverse retains the chosen
component coordinates. An identification of the centralizer with S₃
therefore gives one product map and compatible maps for every subgroup
of either factor.

This is a conditional assembly step for Aschbacher–Smith 13.8.21(1),
printed p.957 (combined manuscript, 1 March 2004). The inner-action
premise and the centralizer identification are explicit obligations;
these theorems do not establish them from the covered-A₆ source setup.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct
variable {G : Type*} [Group G]

/-- Inner action on K* gives generation by K* and its actual centralizer. -/
theorem component_sup_centralizer (H K : Subgroup G)
    (hinner : ∀ h : Source.Hstar H, ∃ k : Source.starImage H K,
      ∀ x : Source.starImage H K,
        h * x.val * h⁻¹ = k.val * x.val * k.val⁻¹) :
    Source.starImage H K ⊔ centralizer (Source.starImage H K : Set (Source.Hstar H)) = ⊤ := by
  apply top_unique
  intro h _
  obtain ⟨k, hk⟩ := hinner h
  have hc : k.val⁻¹ * h ∈ centralizer (Source.starImage H K : Set (Source.Hstar H)) := by
    intro x hx
    calc
      x * (k.val⁻¹ * h) = k.val⁻¹ * (k.val * x * k.val⁻¹) * h := by group
      _ = k.val⁻¹ * (h * x * h⁻¹) * h := by rw [hk ⟨x,hx⟩]
      _ = (k.val⁻¹ * h) * x := by group
  have hm := (Source.starImage H K ⊔ centralizer (Source.starImage H K : Set (Source.Hstar H))).mul_mem
    (mem_sup_left k.property) (mem_sup_right hc)
  simpa only [mul_inv_cancel_left] using hm

private theorem component_disjoint_centralizer (H K : Subgroup G)
    (eK : Source.starImage H K ≃* BinaryLinearThree.Group) :
    Disjoint (Source.starImage H K)
      (centralizer (Source.starImage H K : Set (Source.Hstar H))) := by
  apply disjoint_iff_inf_le.mpr
  intro x hx
  have hc : (⟨x,hx.1⟩ : Source.starImage H K) ∈ center (Source.starImage H K) := by
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (hx.2 y.val y.property)
  have he := (centerCongr eK ⟨⟨x,hx.1⟩,hc⟩).property
  have hz : eK ⟨x,hx.1⟩ = 1 := mem_bot.mp (Matrix.PSL3Two.center_eq_bot.le he)
  exact congrArg Subtype.val (eK.map_eq_one_iff.mp hz)

/-- Multiplication identifies the actual component and its centralizer with H*.
The source must still supply the inner-action premise. -/
noncomputable def componentCentralizerEquiv (H K : Subgroup G)
    (eK : Source.starImage H K ≃* BinaryLinearThree.Group)
    (hinner : ∀ h : Source.Hstar H, ∃ k : Source.starImage H K,
      ∀ x : Source.starImage H K,
        h * x.val * h⁻¹ = k.val * x.val * k.val⁻¹) :
    Source.starImage H K × centralizer (Source.starImage H K : Set (Source.Hstar H)) ≃*
      Source.Hstar H := by
  let f := (Source.starImage H K).subtype.noncommCoprod
    (centralizer (Source.starImage H K : Set (Source.Hstar H))).subtype
    (fun k c => show Commute k.val c.val from c.property k.val k.property)
  apply MulEquiv.ofBijective f
  constructor
  · exact (MonoidHom.noncommCoprod_injective _ _ _).mpr
      ⟨Subtype.val_injective, Subtype.val_injective, by
        simpa only [range_subtype] using component_disjoint_centralizer H K eK⟩
  · apply MonoidHom.range_eq_top.mp
    have hf := MonoidHom.noncommCoprod_range (Source.starImage H K).subtype
      (centralizer (Source.starImage H K : Set (Source.Hstar H))).subtype
      (fun k c => show Commute k.val c.val from c.property k.val k.property)
    exact hf.trans (by simpa only [range_subtype] using component_sup_centralizer H K hinner)

/-- An S₃ identification of that same centralizer gives the product map.
This conditional construction does not assert the missing local geometry. -/
noncomputable def productEquiv (H K : Subgroup G)
    (eK : Source.starImage H K ≃* BinaryLinearThree.Group)
    (eC : centralizer (Source.starImage H K : Set (Source.Hstar H)) ≃* Equiv.Perm (Fin 3))
    (hinner : ∀ h : Source.Hstar H, ∃ k : Source.starImage H K,
      ∀ x : Source.starImage H K,
        h * x.val * h⁻¹ = k.val * x.val * k.val⁻¹) :
    Source.Hstar H ≃* BinaryLinearThree.Group × Equiv.Perm (Fin 3) :=
  (componentCentralizerEquiv H K eK hinner).symm.trans (eK.prodCongr eC)

theorem productEquiv_component (H K : Subgroup G)
    (eK : Source.starImage H K ≃* BinaryLinearThree.Group)
    (eC : centralizer (Source.starImage H K : Set (Source.Hstar H)) ≃* Equiv.Perm (Fin 3))
    (hinner : ∀ h : Source.Hstar H, ∃ k : Source.starImage H K,
      ∀ x : Source.starImage H K,
        h * x.val * h⁻¹ = k.val * x.val * k.val⁻¹)
    (k : Source.starImage H K) :
    productEquiv H K eK eC hinner k.val = (eK k, 1) := by
  have he : componentCentralizerEquiv H K eK hinner (k,1) = k.val := by
    change k.val * 1 = k.val
    exact mul_one _
  rw [← he, productEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  change (eK k, eC 1) = (eK k, 1)
  rw [map_one]

theorem productEquiv_centralizer (H K : Subgroup G)
    (eK : Source.starImage H K ≃* BinaryLinearThree.Group)
    (eC : centralizer (Source.starImage H K : Set (Source.Hstar H)) ≃* Equiv.Perm (Fin 3))
    (hinner : ∀ h : Source.Hstar H, ∃ k : Source.starImage H K,
      ∀ x : Source.starImage H K,
        h * x.val * h⁻¹ = k.val * x.val * k.val⁻¹)
    (c : centralizer (Source.starImage H K : Set (Source.Hstar H))) :
    productEquiv H K eK eC hinner c.val = (1, eC c) := by
  have he : componentCentralizerEquiv H K eK hinner (1,c) = c.val := by
    change 1 * c.val = c.val
    exact one_mul _
  rw [← he, productEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  change (eK 1, eC c) = (1, eC c)
  rw [map_one]


end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct
variable {G : Type*} [Group G] (H K : Subgroup G)
    (eK : Source.starImage H K ≃* BinaryLinearThree.Group)
    (eC : centralizer (Source.starImage H K : Set (Source.Hstar H)) ≃* Equiv.Perm (Fin 3))
    (hinner : ∀ h : Source.Hstar H, ∃ k : Source.starImage H K,
      ∀ x : Source.starImage H K,
        h * x.val * h⁻¹ = k.val * x.val * k.val⁻¹)

/-- Every subgroup of the actual component retains the chosen component
coordinates in the product, including the eventual source L₀* marking. -/
theorem productEquiv_component_subgroup (A : Subgroup (Source.Hstar H))
    (hAK : A ≤ Source.starImage H K) :
    A.map (productEquiv H K eK eC hinner).toMonoidHom =
      ((A.subgroupOf (Source.starImage H K)).map eK.toMonoidHom).prod ⊥ := by
  ext y
  constructor
  · rintro ⟨a,ha,rfl⟩
    change productEquiv H K eK eC hinner a ∈ _
    rw [productEquiv_component H K eK eC hinner ⟨a,hAK ha⟩]
    exact ⟨⟨⟨a,hAK ha⟩,ha,rfl⟩, rfl⟩
  · rintro ⟨⟨k,hk,hky⟩,hy⟩
    refine ⟨k.val,hk,?_⟩
    change productEquiv H K eK eC hinner k.val = y
    rw [productEquiv_component]
    exact Prod.ext hky (mem_bot.mp hy).symm

/-- Every subgroup of the actual centralizer retains the chosen S₃
coordinates; this will mark X* by its order-three image in S₃. -/
theorem productEquiv_centralizer_subgroup (A : Subgroup (Source.Hstar H))
    (hAC : A ≤ centralizer (Source.starImage H K : Set (Source.Hstar H))) :
    A.map (productEquiv H K eK eC hinner).toMonoidHom =
      (⊥ : Subgroup BinaryLinearThree.Group).prod
        ((A.subgroupOf (centralizer (Source.starImage H K : Set (Source.Hstar H)))).map
          eC.toMonoidHom) := by
  ext y
  constructor
  · rintro ⟨a,ha,rfl⟩
    change productEquiv H K eK eC hinner a ∈ _
    rw [productEquiv_centralizer H K eK eC hinner ⟨a,hAC ha⟩]
    exact ⟨rfl, ⟨⟨a,hAC ha⟩,ha,rfl⟩⟩
  · rintro ⟨hy,⟨c,hc,hcy⟩⟩
    refine ⟨c.val,hc,?_⟩
    change productEquiv H K eK eC hinner c.val = y
    rw [productEquiv_centralizer]
    exact Prod.ext (mem_bot.mp hy).symm hcy
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct
