module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.AlternatingSeven.CoverAction
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.AlternatingSeven.Coordinates
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.AlternatingSeven.Rigidity

/-!
# The A₇ and threefold-cover intersection

The quotient map carries the fixed subgroup of `z` onto the actual partition
stabilizer. The intersection `L ∩ M` inherits characteristic two from `H ∩ M`,
so embeds in the central quotient. The concrete A₇ overgroup calculation
identifies its image with the partition stabilizer. Injectivity then identifies
the intersection with the lifted fixed subgroup and gives an isomorphism whose
underlying map is the original central quotient.

`intersection_identification` discharges both of the extra premises in the
original conditional assembly. `exists_partition_identification` accepts any
actual quotient action of cycle type `2³`, so standard coordinates introduce
no extra source hypothesis. The center orders and quotient equivalence are
the genuine model inputs of 1.1.5(3)(d) and Notation A.3.5.

The printed ordinary-maximality shortcut is false; characteristic two supplies
the required restriction on overgroups. For the threefold cover, the
identification is with the image of the intersection, not the full inverse
image of a partition stabilizer, which contains the odd center.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 2.3.9(7)(c), printed pp.525–526.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.AlternatingSeven

open Subgroup

variable {G : Type*} [Group G]

/-- The conditional assembly, retained as an interface. The source branch
below supplies both characteristic two and overgroup rigidity. -/
theorem intersection_identification_of_even_and_rigidity
    {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (e : (L ⧸ center L) ≃* A7)
    (hZ : Nat.card (center L) = 1 ∨ Nat.card (center L) = 3)
    (α : MulAut L) (hα : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹)
    (ha : ActsAsTripleSwap e α) (hN : M.subgroupOf L ∈ Chapter1.He L)
    (hrigidity : ∀ N : Subgroup A7, N ∈ Chapter1.He A7 →
      alternatingStabilizer ≤ N → N = alternatingStabilizer) :
    (M.subgroupOf L).map (quotientMap e) = alternatingStabilizer ∧
      L ⊓ M = L ⊓ centralizer ({z} : Set G) ∧
      ∃ f : M.subgroupOf L ≃* alternatingStabilizer,
        ∀ x : M.subgroupOf L, (f x : A7) = quotientMap e (x : L) := by
  let : Finite G := h.finite
  have hinj := quotientMap_injective_on_even e hZ hN
  have himage := hrigidity _ (image_even e hZ hN)
    (stabilizer_le_intersection_image h e hZ α hα ha)
  have hfixed : M.subgroupOf L = fixedSubgroup α := by
    apply le_antisymm _ (fixedSubgroup_le_intersection h α hα)
    intro x hx
    have hximage : quotientMap e x ∈ (fixedSubgroup α).map (quotientMap e) := by
      rw [fixedSubgroup_image e hZ α (h.action_sq α hα) ha, ← himage]
      exact mem_map.mpr ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hq⟩ := hximage
    have hyN := fixedSubgroup_le_intersection h α hα hy
    have he : (⟨y, hyN⟩ : M.subgroupOf L) = ⟨x, hx⟩ := hinj hq
    have hyx : y = x := congrArg Subtype.val he
    exact hyx ▸ hy
  refine ⟨himage, ?_, ?_⟩
  · apply le_antisymm
    · rintro x ⟨hxL, hxM⟩
      refine ⟨hxL, mem_centralizer_singleton_iff.mpr ?_⟩
      have hf : (⟨x, hxL⟩ : L) ∈ fixedSubgroup α :=
        hfixed ▸ (show (⟨x, hxL⟩ : L) ∈ M.subgroupOf L from hxM)
      change α ⟨x, hxL⟩ = ⟨x, hxL⟩ at hf
      have he := hα ⟨x, hxL⟩
      rw [hf] at he
      exact (mul_inv_eq_iff_eq_mul.mp he.symm).symm
    · exact inf_le_inf_left _ h.centralizer_le
  · refine ⟨(imageEquiv e (M.subgroupOf L) hinj).trans
      (MulEquiv.subgroupCongr himage), ?_⟩
    intro x
    rfl

/-- The A₇ branch of 2.3.9(7)(c) in coordinates adapted to the involution.
The quotient map is the actual central quotient of the component, including
its order-three kernel in the nonsplit-cover case. -/
theorem intersection_identification
    {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (e : (L ⧸ center L) ≃* A7)
    (hZ : Nat.card (center L) = 1 ∨ Nat.card (center L) = 3)
    (α : MulAut L) (hα : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹)
    (ha : ActsAsTripleSwap e α) :
    (M.subgroupOf L).map (quotientMap e) = alternatingStabilizer ∧
      L ⊓ M = L ⊓ centralizer ({z} : Set G) ∧
      ∃ f : M.subgroupOf L ≃* alternatingStabilizer,
        ∀ x : M.subgroupOf L, (f x : A7) = quotientMap e (x : L) :=
  intersection_identification_of_even_and_rigidity h e hZ α hα ha
    (intersection_even h) characteristicTwo_overgroup_eq

/-- The source cycle-type formulation of the A₇ branch. Relabeling the
quotient chooses the partition determined by `z`, while retaining its lifted
action on `L` and the quotient map on every element of the intersection. -/
theorem exists_partition_identification
    {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (e : (L ⧸ center L) ≃* A7)
    (hZ : Nat.card (center L) = 1 ∨ Nat.card (center L) = 3)
    (α : MulAut L) (hα : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹)
    (σ : S7) (hσ : σ.cycleType = {2, 2, 2})
    (ha : ∀ x : L, (quotientMap e (α x) : S7) =
      σ * (quotientMap e x : S7) * σ⁻¹) :
    ∃ e' : (L ⧸ center L) ≃* A7, ActsAsTripleSwap e' α ∧
      (M.subgroupOf L).map (quotientMap e') = alternatingStabilizer ∧
      L ⊓ M = L ⊓ centralizer ({z} : Set G) ∧
      ∃ f : M.subgroupOf L ≃* alternatingStabilizer,
        ∀ x : M.subgroupOf L, (f x : A7) = quotientMap e' (x : L) := by
  obtain ⟨e', he'⟩ := exists_standard_coordinates e α σ hσ ha
  exact ⟨e', he', intersection_identification h e' hZ α hα he'⟩

end CFSG.Quasithin.Chapter2.ComponentRefinement.AlternatingSeven
end
