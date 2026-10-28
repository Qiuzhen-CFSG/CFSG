module

public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Structure.CentralKernel.Interface

/-!
# The marked radical in the actual SL₃ model

Compose the quotient star map with the source model, retaining the original
quotient I/P. The q² order is transported through the actual image maps.
The source commutator equality puts every natural-module displacement in
the marked point, and the G.2.1 centralizer calculation shows that point
is fixed. These are the literal model inputs consumed by the root lift.

Source: Aschbacher–Smith G.2.5(1,3), printed pp.335–336.
-/

@[expose] public section
open Subgroup Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.CentralKernel
open Setup
variable {G : Type*} [Group G] [Finite G]
  {D : Setup G} {F : Type*} [Field F] [Finite F]
  {n : ℕ} {g h : G} (d : Hypothesis D F n g h)
  [((WProduct D g h).subgroupOf (I D g h)).Normal]

def rootModelMap (hUT : D.U ≤ D.T)
    (hstar : D.star (I D g h) = D.star D.L) : Quotient D g h →* SL(3, F) :=
  d.model.toMonoidHom.comp (starMap d hUT hstar)

def rootModelRadical (hUT : D.U ≤ D.T)
    (hstar : D.star (I D g h) = D.star D.L) : Subgroup SL(3, F) :=
  (image D g h D.U).map (rootModelMap d hUT hstar)

theorem rootModelMap_surjective (hUT : D.U ≤ D.T)
    (hstar : D.star (I D g h) = D.star D.L) :
    Function.Surjective (rootModelMap d hUT hstar) :=
  d.model.surjective.comp (starMap_surjective d hUT hstar)

theorem rootModelRadical_card (hUT : D.U ≤ D.T)
    (hstar : D.star (I D g h) = D.star D.L)
    (eU : D.star D.U ≃* Multiplicative (Fin 2 → F)) :
    Nat.card (rootModelRadical d hUT hstar) = Nat.card F ^ 2 := by
  have hm := map_image_starMap d hUT hstar D.U
    (show D.U ≤ I D g h from le_sup_left.trans le_sup_left)
  rw [← Subgroup.map_map] at hm
  change Nat.card ((image D g h D.U).map
    (d.model.toMonoidHom.comp (starMap d hUT hstar))) = _
  rw [← Subgroup.map_map, card_map_of_injective d.model.injective]
  rw [← card_map_of_injective (f := (D.star D.L).subtype) (subtype_injective _), hm]
  rw [Nat.card_congr eU.toEquiv]
  change Nat.card (Fin 2 → F) = _
  simp only [Nat.card_fun, Nat.card_fin]

theorem rootModelRadical_displacement (hUT : D.U ≤ D.T)
    (hstar : D.star (I D g h) = D.star D.L)
    (hmove : ⁅D.V, D.U⁆ = D.V₁) :
    ∀ a ∈ rootModelRadical d hUT hstar, ∀ v : Fin 3 → F,
      a.val *ᵥ v - v ∈ d.point := by
  rintro a ⟨z, ⟨u, hu, rfl⟩, rfl⟩ v
  obtain ⟨w, hw⟩ := d.coordinates.surjective (Multiplicative.ofAdd v)
  have hw' : (d.coordinates w).toAdd = v := hw
  let w' : D.V := ⟨(u : G) * w * (u : G)⁻¹,
    (mem_normalizer_iff.mp (d.I_normalizes hUT u.property) w).mp w.property⟩
  have hc : ((w' * w⁻¹ : D.V) : G) ∈ D.V₁ := by
    rw [← hmove, commutator_comm]
    exact commutator_mem_commutator hu w.property
  have hp := (d.point_mem (w' * w⁻¹)).mp hc
  have he := d.IStarProjection_equivariant hUT hstar u w
  change (d.coordinates w').toAdd = _ at he
  simpa only [map_mul, map_inv, toAdd_mul, toAdd_inv, he, hw', sub_eq_add_neg,
    rootModelMap, MonoidHom.comp_apply, starMap_projection, MulEquiv.coe_toMonoidHom] using hp

theorem rootModelRadical_fixes_point (hUT : D.U ≤ D.T)
    (hstar : D.star (I D g h) = D.star D.L) :
    ∀ a ∈ rootModelRadical d hUT hstar, ∀ v ∈ d.point, a.val *ᵥ v = v := by
  rintro a ⟨z, ⟨u, hu, rfl⟩, rfl⟩ v hv
  obtain ⟨w, hw⟩ := d.coordinates.surjective (Multiplicative.ofAdd v)
  have hw' : (d.coordinates w).toAdd = v := hw
  have hw₁ : (w : G) ∈ D.V₁ := (d.point_mem w).mpr (hw'.symm ▸ hv)
  have hc := d.setup.U_le_centralizer_point hu (w : G) hw₁
  change (w : G) * (u : G) = (u : G) * (w : G) at hc
  have he : (u : G) * w * (u : G)⁻¹ = w := by
    rw [← hc, mul_inv_cancel_right]
  have he' : (⟨(u : G) * w * (u : G)⁻¹,
      (mem_normalizer_iff.mp (d.I_normalizes hUT u.property) w).mp w.property⟩ : D.V) = w :=
    Subtype.ext he
  have hact := d.IStarProjection_equivariant hUT hstar u w
  rw [he', hw'] at hact
  exact hact.symm

end CFSG.Quasithin.ChapterG.Section02.LinearThree.CentralKernel
