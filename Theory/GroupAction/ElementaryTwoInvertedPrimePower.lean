module
public import Theory.GroupAction.HyperplaneCommutatorGeneration
public import Mathlib.Tactic.Group
/-!
# A cyclic odd-prime-power subgroup detected by an elementary actor

Hyperplane centralizer commutators detect every nontrivial elementary
coprime action. A moved element in one such centralizer gives a nontrivial
commutator inverted by an involution. Its fixing hyperplane has index two,
so every original actor fixes or inverts the same cyclic subgroup.
Source: the solvable branch of Aschbacher–Smith E.2.7, printed p.218.
-/
public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace Theory.GroupAction
variable {G : Type*} [Group G] [Finite G]

/-- A moved odd-prime group under an elementary two-group contains a cyclic
prime-power subgroup on which the actors induce precisely inversion or identity. -/
theorem exists_inverted_prime_power_line {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (R V : Subgroup G) (hR : IsPGroup p R) [IsElementaryAbelian 2 V]
    (hVR : V ≤ normalizer (R : Set G)) (hne : ⁅R,V⁆ ≠ ⊥) :
    ∃ (g v : G) (a : ℕ), g ∈ R ∧ v ∈ V ∧ 0 < a ∧ orderOf g = p ^ a ∧
      v * g * v⁻¹ = g⁻¹ ∧
      (∀ w ∈ V, w * g * w⁻¹ = g ∨ w * g * w⁻¹ = g⁻¹) := by
  have hex : ∃ B : Subgroup V, B.index = 2 ∧
      ⁅R ⊓ centralizer (B.map V.subtype : Set G), V⁆ ≠ ⊥ := by
    by_contra! h
    apply hne
    rw [← iSup_hyperplane_centralizer_commutator hp R V hR hVR]
    apply le_bot_iff.mp
    exact iSup₂_le fun B hB => (h B hB).le
  obtain ⟨B,hB,hmove⟩ := hex
  let C := R ⊓ centralizer (B.map V.subtype : Set G)
  have hex : ∃ x ∈ C, ∃ v ∈ V, v*x ≠ x*v := by
    by_contra! h
    apply hmove
    exact commutator_eq_bot_iff_le_centralizer.mpr (fun x hx v hv => h x hx v hv)
  obtain ⟨x,hx,v,hv,hm⟩ := hex
  let g := v*x*v⁻¹*x⁻¹
  have hv2 : v*v = 1 := by simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) v hv
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have hgR : g ∈ R := R.mul_mem ((mem_normalizer_iff.mp (hVR hv) x).mp hx.1) (R.inv_mem hx.1)
  have hg1 : g ≠ 1 := by
    intro he
    apply hm
    exact commutatorElement_eq_one_iff_mul_comm.mp he
  have hinv : v*g*v⁻¹ = g⁻¹ := by
    dsimp only [g]
    simp only [mul_inv_rev, inv_inv, hvi]
    simp only [← mul_assoc, hv2, one_mul]
  have hBfix : ∀ w ∈ B.map V.subtype, w*g*w⁻¹ = g := by
    intro w hw
    have hwV : w ∈ V := map_subtype_le B hw
    have hwv : w*v = v*w := congrArg Subtype.val (mul_comm (⟨w,hwV⟩ : V) ⟨v,hv⟩)
    have hwx : w*x = x*w := hx.2 w hw
    have hwc : v ∈ centralizer ({w} : Set G) := mem_centralizer_singleton_iff.mpr hwv.symm
    have hxc : x ∈ centralizer ({w} : Set G) := mem_centralizer_singleton_iff.mpr hwx.symm
    have hgc : g ∈ centralizer ({w} : Set G) :=
      (centralizer ({w} : Set G)).mul_mem
        ((centralizer ({w} : Set G)).mul_mem
          ((centralizer ({w} : Set G)).mul_mem hwc hxc)
          ((centralizer ({w} : Set G)).inv_mem hwc))
        ((centralizer ({w} : Set G)).inv_mem hxc)
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hgc).symm
  have hvB : (⟨v,hv⟩ : V) ∉ B := by
    intro hvB
    exact hm (hx.2 v (mem_map_of_mem V.subtype hvB))
  obtain ⟨a,ha⟩ := (IsPGroup.iff_orderOf).mp hR ⟨g,hgR⟩
  have horder : orderOf g = p ^ a := by simpa only [Subgroup.orderOf_mk] using ha
  have ha0 : 0 < a := by
    by_contra! ha0
    have he : a = 0 := by omega
    exact hg1 (orderOf_eq_one_iff.mp (by simpa only [he,pow_zero] using horder))
  refine ⟨g,v,a,hgR,hv,ha0,horder,hinv,?_⟩
  intro w hw
  by_cases hwB : (⟨w,hw⟩ : V) ∈ B
  · exact Or.inl (hBfix w (mem_map_of_mem V.subtype hwB))
  · have hvw : (⟨v,hv⟩ : V) * ⟨w,hw⟩ ∈ B :=
      (B.mul_mem_iff_of_index_two hB).mpr (iff_of_false hvB hwB)
    have hfix := hBfix (v*w) (mem_map_of_mem V.subtype hvw)
    right
    have hh := congrArg (fun y : G => v*y*v⁻¹) hfix
    rw [hinv] at hh
    have he : v * (v*w*g*(v*w)⁻¹) * v⁻¹ = w*g*w⁻¹ := by
      simp only [mul_inv_rev, hvi]
      simp only [← mul_assoc, hv2, one_mul]
      rw [mul_assoc, hv2, mul_one]
    exact he.symm.trans hh
end Theory.GroupAction
