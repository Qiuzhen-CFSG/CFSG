module

public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.QuotientConstruction.AffineQuotient
/-!
# Binary differences recovered from native octads

An octad supported on two parts of the standard trio cuts those parts by
parallel affine planes (the two whole parts are the constant-cut cases).
We check this against every native Golay octad, computing each normal from
its values at zero and the three coordinate vectors. Three displayed native
octads separate the coordinates. Consequently two pairs of points have equal
vector differences exactly when every supported octad separates both pairs
or neither. This characterization is invariant under the trio stabilizer.

Source context: Aschbacher, *Sporadic Groups*, Chapter 7, Lemma 20.2,
printed p.97. All finite checks use the literal point table and native blocks.
-/

@[expose] public section

open scoped Pointwise

namespace Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.QuotientConstruction
namespace CoverageGeometry

noncomputable def dot (n v : Vector) : ZMod 2 := ∑ k, n k * v k

theorem dot_add (n u v : Vector) : dot n (u + v) = dot n u + dot n v := by
  simp [dot, mul_add, Finset.sum_add_distrib]

noncomputable def testBlock (i j k : Fin 3) : Finset (Fin 24) :=
  (Finset.univ.filter fun v : Vector => v k = 0).image (fun v => point (i,v)) ∪
  (Finset.univ.filter fun v : Vector => v k = 0).image (fun v => point (j,v))

private def testBlockIndex : Fin 3 → Fin 3 → Fin 3 → Fin 759 :=
  ![![![0,0,0], ![500,231,382], ![468,144,344]],
    ![![500,231,382], ![0,0,0], ![581,562,579]],
    ![![468,144,344], ![581,562,579], ![0,0,0]]]

set_option maxRecDepth 100000 in
private theorem testBlock_eq : ∀ i j : Fin 3, i ≠ j → ∀ k,
    testBlock i j k = m24BlockAt (testBlockIndex i j k) := by decide +kernel

theorem testBlock_mem (i j : Fin 3) (hij : i ≠ j) (k : Fin 3) :
    testBlock i j k ∈ m24Blocks := by
  rw [testBlock_eq i j hij k]
  exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩

theorem testBlock_subset (i j k : Fin 3) :
    testBlock i j k ⊆ standardTrioOctad i ∪ standardTrioOctad j := by
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_union_left _ (point_mem_octad _ _)
  · obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_union_right _ (point_mem_octad _ _)

theorem mem_testBlock_left (i j k : Fin 3) (hij : i ≠ j) (v : Vector) :
    point (i,v) ∈ testBlock i j k ↔ v k = 0 := by
  simp [testBlock, point.injective.eq_iff, Prod.mk.injEq, hij, eq_comm]

theorem mem_testBlock_right (i j k : Fin 3) (hij : i ≠ j) (v : Vector) :
    point (j,v) ∈ testBlock i j k ↔ v k = 0 := by
  simp [testBlock, point.injective.eq_iff, Prod.mk.injEq, hij, eq_comm]

private noncomputable def bit (b : Fin 759) (i : Fin 3) (v : Vector) : ZMod 2 :=
  if point (i,v) ∈ m24BlockAt b then 0 else 1

private noncomputable def normal (b : Fin 759) (i : Fin 3) : Vector :=
  fun k => bit b i (Pi.single k 1) + bit b i 0

set_option maxRecDepth 100000 in
private theorem native_cuts : ∀ b : Fin 759, ∀ i j : Fin 3, i ≠ j →
    (∀ x : Fin 24, x ∈ m24BlockAt b → x ∈ standardTrioOctad i ∪ standardTrioOctad j) →
      (∀ v, point (i,v) ∈ m24BlockAt b ↔ dot (normal b i) v = bit b i 0) ∧
      (∀ v, point (j,v) ∈ m24BlockAt b ↔ dot (normal b i) v = bit b j 0) := by
  decide +kernel

theorem same_difference_iff (i j : Fin 3) (hij : i ≠ j) (u v w z : Vector) :
    u + v = w + z ↔
    ∀ B ∈ m24Blocks, B ⊆ standardTrioOctad i ∪ standardTrioOctad j →
      ((point (i,u) ∈ B ↔ point (i,v) ∈ B) ↔
       (point (j,w) ∈ B ↔ point (j,z) ∈ B)) := by
  constructor
  · intro huv B hB hsub
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨hi, hj⟩ := native_cuts b i j hij (fun _ hx => hsub hx)
    let n := normal b i
    simp only [hi, hj]
    have he : dot n u + dot n v = dot n w + dot n z := by
      rw [← dot_add, ← dot_add, huv]
    exact (show ∀ a b c d r s : ZMod 2, a + b = c + d →
      ((a = r ↔ b = r) ↔ (c = s ↔ d = s)) by decide) _ _ _ _ _ _ he
  · intro h
    ext k
    have hk := h (testBlock i j k) (testBlock_mem i j hij k) (testBlock_subset i j k)
    rw [mem_testBlock_left _ _ _ hij, mem_testBlock_left _ _ _ hij,
      mem_testBlock_right _ _ _ hij, mem_testBlock_right _ _ _ hij] at hk
    exact (show ∀ a b c d : ZMod 2,
      ((a = 0 ↔ b = 0) ↔ (c = 0 ↔ d = 0)) → a + b = c + d by decide) _ _ _ _ hk

end CoverageGeometry
end Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.QuotientConstruction
