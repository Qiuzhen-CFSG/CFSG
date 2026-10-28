module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.FourGroup
public import Theory.GroupTheory.PerfectCentralCoverExistence

/-!
# Lifting the rank-one centralizer calculation

Maps from a perfect group through a central extension lift uniquely. Applied
to the component map L → L⁺, this proves that C_{I⁺}(L⁺) is trivial for the
actual quotient I⁺ = I/C_I(L), without discarding a possible central cover.
A trivial C_{S⁺}(Y⁺) then pulls back to C_S(Y) = C_S(L). The nontrivial V₁
action contradicts this equality.

These are transfer lemmas, not the sporadic model calculations. Source:
Aschbacher--Smith, combined manuscript (1 March 2004), 15.3.43(c),(e) and
the sporadic paragraph, printed pp.1139--1140.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.SporadicModels
variable {G : Type*} [Group G] {I L : Subgroup G}

/-- Perfectness removes the central error when an element centralizes the component image. -/
theorem centralizes_component_of_centralizes_image
    (d : ComponentAction I L) [Group.IsPerfect L] (x : I)
    (hx : d.quotientMap x ∈ centralizer (d.image L : Set d.Quotient)) :
    (x : G) ∈ centralizer (L : Set G) := by
  let a : MulAut L := L.normalizerMonoidHom ⟨x, d.normalizes x.property⟩
  have he : a.toMonoidHom = MonoidHom.id L := by
    apply PerfectCentralCovering.monoidHom_eq_of_isPerfect_of_comp_eq
      d.componentMap (by rw [d.componentMap_ker])
    ext y
    change d.quotientMap (x * ⟨y, d.component_le y.property⟩ * x⁻¹) =
      d.quotientMap ⟨y, d.component_le y.property⟩
    rw [map_mul, map_mul, map_inv]
    have hc := hx (d.quotientMap ⟨y, d.component_le y.property⟩)
      (mem_map_of_mem d.quotientMap y.property)
    rw [← hc, mul_inv_cancel_right]
  intro y hy
  have h := congrArg Subtype.val (DFunLike.congr_fun he ⟨y, hy⟩)
  change (x : G) * y * (x : G)⁻¹ = y at h
  exact (mul_inv_eq_iff_eq_mul.mp h).symm

/-- The quotient by the actual component centralizer acts faithfully on the simple image, including when the component has nontrivial center. -/
theorem component_image_centralizer_eq_bot
    (d : ComponentAction I L) [Group.IsPerfect L] :
    centralizer (d.image L : Set d.Quotient) = ⊥ := by
  apply bot_unique
  intro x hx
  obtain ⟨y, rfl⟩ := d.quotientMap_surjective x
  exact (QuotientGroup.eq_one_iff y).mpr
    (centralizes_component_of_centralizes_image d y hx)

/-- A trivial Sylow centralizer downstairs gives the required equality upstairs by pulling back the actual kernel C_I(L). -/
theorem upstairs_centralizer_eq_of_image_centralizer_eq_bot
    (d : ComponentAction I L) {S Y : Subgroup G} (hSI : S ≤ I) (hYL : Y ≤ L)
    (hC : d.image S ⊓ centralizer (d.image Y : Set d.Quotient) = ⊥) :
    S ⊓ centralizer (Y : Set G) = S ⊓ centralizer (L : Set G) := by
  apply le_antisymm
  · rintro x ⟨hxS, hxC⟩
    refine ⟨hxS, ?_⟩
    let xi : I := ⟨x, hSI hxS⟩
    have hxq : d.quotientMap xi ∈ d.image S ⊓
        centralizer (d.image Y : Set d.Quotient) := by
      refine ⟨mem_map_of_mem d.quotientMap hxS, ?_⟩
      rintro _ ⟨y, hy, rfl⟩
      have hc : y * xi = xi * y := Subtype.ext (hxC y hy)
      simpa only [map_mul] using congrArg d.quotientMap hc
    rw [hC] at hxq
    exact (QuotientGroup.eq_one_iff xi).mp hxq
  · exact inf_le_inf_left S (centralizer_le hYL)

/-- Equality of the quotient centralizers yields the upstairs equality after perfectness proves faithfulness on the component image. -/
theorem upstairs_centralizer_eq_of_image_centralizers_eq
    (d : ComponentAction I L) [Group.IsPerfect L] {S Y : Subgroup G}
    (hSI : S ≤ I) (hYL : Y ≤ L)
    (hC : d.image S ⊓ centralizer (d.image Y : Set d.Quotient) =
      d.image S ⊓ centralizer (d.image L : Set d.Quotient)) :
    S ⊓ centralizer (Y : Set G) = S ⊓ centralizer (L : Set G) := by
  apply upstairs_centralizer_eq_of_image_centralizer_eq_bot d hSI hYL
  rw [hC, component_image_centralizer_eq_bot d, inf_bot_eq]

/-- Perfectness of the original component follows from its relative component assertion. -/
theorem reduced_component_perfect {Y S M I L V₁ V₂ : Subgroup G}
    (c : ReducedConfiguration Y S M I L V₁ V₂) : Group.IsPerfect L := by
  let : Theory.GroupTheory.IsQuasisimple (L.subgroupOf I) := c.component.2
  exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe c.component_le).toMonoidHom)
    (subgroupOfEquivOfLe c.component_le).surjective

/-- The nontrivial V₁-action forces a nontrivial centralizer in the actual quotient. A model calculation showing this centralizer trivial therefore contradicts the reduced configuration. -/
theorem reduced_image_centralizer_ne_bot {Y S M I L V₁ V₂ : Subgroup G}
    (c : ReducedConfiguration Y S M I L V₁ V₂) :
    c.toComponentAction.image S ⊓
      centralizer (c.toComponentAction.image Y : Set c.toComponentAction.Quotient) ≠ ⊥ := by
  intro hC
  have hSI : S ≤ I := le_sup_right.trans c.minimal.1.1.2
  have he := upstairs_centralizer_eq_of_image_centralizer_eq_bot
    c.toComponentAction hSI c.y_le_component hC
  have hV : V₁ ≤ S ⊓ centralizer (Y : Set G) :=
    le_inf c.plane_one_le (commutator_eq_bot_iff_le_centralizer.mp c.plane_one_centralizes)
  rw [he] at hV
  exact c.plane_one_acts
    (commutator_eq_bot_iff_le_centralizer.mpr (hV.trans inf_le_right))

end CFSG.Quasithin.Chapter15.Section03.RankOne.SporadicModels
