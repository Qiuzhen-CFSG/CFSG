module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PointPairCommutator

/-!
# Derived lines and intersections of the original HS point cores

The square line of each original point core contains its commutators. Thus
an element shared by two distinct point cores centralizes the whole seed:
its commutator with each seed element lies in two distinct involution lines.
The shared element is consequently in the full normalizer core and has
square one, placing it in the original seed itself.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

/-- Commutators in the original point core lie in its distinguished
involution line. -/
theorem TypeAt.point_core_commutator_mem (h : TypeAt z V) (a b : G)
    (ha : a ∈ (involutionCentralizer z).pCoreIn 2)
    (hb : b ∈ (involutionCentralizer z).pCoreIn 2) :
    ⁅a, b⁆ ∈ zpowers z := by
  let Q := (involutionCentralizer z).pCoreIn 2
  have hs := (zpowers z).mul_mem
    ((zpowers z).mul_mem (h.centralizer_core_square_mem a ha)
      (h.centralizer_core_square_mem (a⁻¹ * b) (Q.mul_mem (Q.inv_mem ha) hb)))
    ((zpowers z).inv_mem (h.centralizer_core_square_mem b hb))
  have he : a ^ 2 * (a⁻¹ * b) ^ 2 * (b ^ 2)⁻¹ = ⁅a, b⁆ := by
    simp only [pow_two, commutatorElement_def, mul_inv_rev]
    group
  exact he ▸ hs

private theorem equal_one_of_two_lines {u v q : G}
    (hu : orderOf u = 2) (hv : orderOf v = 2) (huv : u ≠ v)
    (hqu : q ∈ zpowers u) (hqv : q ∈ zpowers v) : q = 1 := by
  classical
  have cases {x y : G} (hx : orderOf x = 2) (hy : y ∈ zpowers x) :
      y = 1 ∨ y = x := by
    rw [mem_zpowers_iff_mem_range_orderOf, hx] at hy
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hy
    have hn2 : n < 2 := Finset.mem_range.mp hn
    interval_cases n <;> simp
  rcases cases hu hqu with he | he
  · exact he
  rcases cases hv hqv with hf | hf
  · exact hf
  exact (huv (he.symm.trans hf)).elim

/-- The two original point cores at distinct nonidentity seed points meet
in precisely the whole original elementary-eight seed. -/
theorem TypeAt.distinct_point_cores_intersection (h : TypeAt z V)
    (u v : G) (hu : u ∈ V) (hv : v ∈ V) (hu1 : u ≠ 1) (hv1 : v ≠ 1)
    (huv : u ≠ v) :
    (involutionCentralizer u).pCoreIn 2 ⊓ (involutionCentralizer v).pCoreIn 2 = V := by
  let huT := h.at_seed_point u hu hu1
  let hvT := h.at_seed_point v hv hv1
  have huV : V ≤ (involutionCentralizer u).pCoreIn 2 := by
    change V ≤ (pCore 2 (involutionCentralizer u)).map (involutionCentralizer u).subtype
    rw [← huT.centralizer_fitting]
    exact huT.seed_le_core
  have hvV : V ≤ (involutionCentralizer v).pCoreIn 2 := by
    change V ≤ (pCore 2 (involutionCentralizer v)).map (involutionCentralizer v).subtype
    rw [← hvT.centralizer_fitting]
    exact hvT.seed_le_core
  apply le_antisymm ?_ (le_inf huV hvV)
  rintro q ⟨hqu, hqv⟩
  have hq2 : q ^ 2 = 1 := equal_one_of_two_lines huT.involution hvT.involution huv
    (huT.centralizer_core_square_mem q hqu) (hvT.centralizer_core_square_mem q hqv)
  have hqC : q ∈ centralizer (V : Set G) := by
    intro w hw
    have hc : ⁅q, w⁆ = 1 := equal_one_of_two_lines huT.involution hvT.involution huv
      (huT.point_core_commutator_mem q w hqu (huV hw))
      (hvT.point_core_commutator_mem q w hqv (hvV hw))
    exact (commutatorElement_eq_one_iff_commute.mp hc).eq.symm
  rw [h.seed_centralizer] at hqC
  obtain ⟨qM, hqM, rfl⟩ := hqC
  have hqO : qM ∈ (omega (pCore 2 (normalizer (V : Set G))) (p := 2) 1).map
      (pCore 2 (normalizer (V : Set G))).subtype := by
    refine ⟨⟨qM, hqM⟩, subset_closure ?_, rfl⟩
    change (⟨qM, hqM⟩ : pCore 2 (normalizer (V : Set G))) ^ (2 ^ 1) = 1
    apply Subtype.ext
    apply Subtype.ext
    exact hq2
  rw [← h.seed_eq_omega_normalizer_core] at hqO
  exact hqO

end CFSG.Quasithin.HigmanSims
