module

public import Mathlib.Algebra.Group.Subgroup.Order
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Transporting maximal subgroups into element centralizers

An ambient group equivalence preserves maximality. Thus a maximal subgroup
whose image centralizes an element with proper centralizer maps onto that
centralizer. A bound for the subgroup center then transfers to the centralizer.

These are elementary subgroup-lattice and homomorphism arguments. They allow
local subgroup certificates to be used without a separate centralizer-order
calculation; a concrete application is the ATLAS Lyons involution subgroup.
-/

namespace Subgroup
variable {G K : Type*} [Group G] [Group K]

/-- A maximal subgroup transported inside a proper element centralizer equals it. -/
public theorem map_eq_centralizer_of_isCoatom (e : G ≃* K) (H : Subgroup G) {t : G} {a : K}
    (hmax : IsCoatom H) (hle : H ≤ centralizer {t})
    (ht : e t = a) (hproper : centralizer ({a} : Set K) ≠ ⊤) :
    H.map e.toMonoidHom = centralizer {a} := by
  have hm : IsCoatom (H.map e.toMonoidHom) := (OrderIso.isCoatom_iff e.mapSubgroup H).mpr hmax
  apply ((hm.le_iff_eq hproper).mp ?_).symm
  rintro x ⟨y, hy, rfl⟩
  apply mem_centralizer_singleton_iff.mpr
  change e y * a = a * e y
  rw [← ht, ← map_mul, ← map_mul]
  exact congrArg e (mem_centralizer_singleton_iff.mp (hle hy))

/-- Transport a two-element bound for the center along an ambient equivalence. -/
public theorem center_bound_of_map_eq (e : G ≃* K) (H : Subgroup G) (L : Subgroup K) (t : G)
    (hmap : H.map e.toMonoidHom = L)
    (hcenter : ∀ z : H, z ∈ center H → (z : G) = 1 ∨ (z : G) = t) :
    ∀ z : L, z ∈ center L → (z : K) = 1 ∨ (z : K) = e t := by
  intro z hz
  have hzm : (z : K) ∈ H.map e.toMonoidHom := hmap.symm ▸ z.property
  obtain ⟨x, hx, hex⟩ := hzm
  change e x = (z : K) at hex
  have hxc : (⟨x, hx⟩ : H) ∈ center H := by
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    apply e.injective
    change e ((y : G) * x) = e (x * (y : G))
    simp only [map_mul]
    have hey : e (y : G) ∈ L := hmap ▸ mem_map.mpr ⟨y, y.property, rfl⟩
    have heq := congrArg Subtype.val (mem_center_iff.mp hz (⟨e y, hey⟩ : L))
    change e (y : G) * (z : K) = (z : K) * e (y : G) at heq
    simpa only [← hex] using heq
  rcases hcenter ⟨x, hx⟩ hxc with hx1 | hxt
  · left
    change x = 1 at hx1
    calc (z : K) = e x := hex.symm
         _ = 1 := by rw [hx1, map_one]
  · right
    calc (z : K) = e x := hex.symm
         _ = e t := congrArg e hxt
end Subgroup
