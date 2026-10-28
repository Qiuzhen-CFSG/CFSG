module
public import Theory.Mathieu.M24.LocalGeometry.EvenCatalogue
public import Theory.Mathieu.M24.LocalGeometry.Defs
public import Mathlib.Algebra.Pointwise.Stabilizer

/-!
# Fixed-point geometry of the three normal four-groups

The exact zero-based catalogue rows 1, 2 and 3 have four elements each.
Their full normalizers permute the fixed-point sets of their nonidentity
members. For rows 1 and 2, the only nonempty such set is the common octad;
for row 3, the three sets form the trio used by the subsequent transporter.
Small permutation tables are checked against the certified Sylow enumeration.

Source context: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.43, sporadic paragraph on printed p.1140; GLS3, Table 5.3e.
-/

@[expose] public section
namespace Sporadic.Mathieu.M24LocalGeometry.FourNormalizers
open Subgroup SylowNormalizer.OrderEnumeration
open scoped Pointwise

def rowNumber (r : Fin 3) : Fin 22 := ⟨r.val + 1, by omega⟩
def rowIndex : Fin 3 → Fin 4 → Fin 1024 :=
  ![![0,106,115,14], ![0,106,758,651], ![0,642,106,744]]
noncomputable def rowElement (r : Fin 3) (j : Fin 4) : M24 :=
  (element (rowIndex r j)).val

def rowPoint : Fin 3 → Fin 4 → Fin 24 → Fin 24 :=
  ![![![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23],![0,20,22,3,4,7,15,5,8,9,17,11,18,16,23,6,13,10,12,19,1,21,2,14],![0,22,20,3,4,10,23,17,8,9,5,11,13,12,15,14,18,7,16,19,2,21,1,6],![0,2,1,3,4,17,14,10,8,9,7,11,16,18,6,23,12,5,13,19,22,21,20,15]],
    ![![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23],![0,20,22,3,4,7,15,5,8,9,17,11,18,16,23,6,13,10,12,19,1,21,2,14],![11,22,20,19,21,17,14,10,9,8,7,0,13,12,6,23,18,5,16,3,2,4,1,15],![11,2,1,19,21,10,23,17,9,8,5,0,16,18,15,14,12,7,13,3,22,4,20,6]],
    ![![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23],![11,1,2,19,21,7,15,5,9,8,17,0,12,13,23,6,16,10,18,3,20,4,22,14],![0,20,22,3,4,7,15,5,8,9,17,11,18,16,23,6,13,10,12,19,1,21,2,14],![11,20,22,19,21,5,6,7,9,8,10,0,18,16,14,15,13,17,12,3,1,4,2,23]]]

private theorem rowPoint_spec : ∀ r j x, rowPoint r j x = point (rowIndex r j) x := by
  decide +kernel

theorem rowElement_apply (r : Fin 3) (j : Fin 4) (x : Fin 24) :
    (rowElement r j).val x = rowPoint r j x := by
  rw [rowPoint_spec]
  exact element_apply _ _

def rowMul : Fin 4 → Fin 4 → Fin 4 :=
  ![![0,1,2,3], ![1,0,3,2], ![2,3,0,1], ![3,2,1,0]]

theorem rowElement_mul (r : Fin 3) (j k : Fin 4) :
    rowElement r j * rowElement r k = rowElement r (rowMul j k) := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  simp only [Subgroup.coe_mul, Equiv.Perm.mul_apply, rowElement_apply]
  revert r j k x
  decide +kernel

theorem rowElement_zero (r : Fin 3) : rowElement r 0 = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change (rowElement r 0).val x = x
  rw [rowElement_apply]
  revert r x
  decide +kernel

theorem rowElement_inv (r : Fin 3) (j : Fin 4) : (rowElement r j)⁻¹ = rowElement r j := by
  apply inv_eq_of_mul_eq_one_right
  rw [rowElement_mul, show rowMul j j = 0 by fin_cases j <;> rfl, rowElement_zero]

private noncomputable def rowSubgroup (r : Fin 3) : Subgroup M24 where
  carrier := Set.range (rowElement r)
  one_mem' := ⟨0, rowElement_zero r⟩
  mul_mem' := by
    rintro _ _ ⟨j, rfl⟩ ⟨k, rfl⟩
    exact ⟨rowMul j k, (rowElement_mul r j k).symm⟩
  inv_mem' := by
    rintro _ ⟨j, rfl⟩
    exact ⟨j, (rowElement_inv r j).symm⟩

private theorem rowElement_generator (r : Fin 3) (j : Fin 6) :
    (element (EvenCatalogue.generatorIndex (rowNumber r) j)).val =
      rowElement r (![1,2,0,0,0,0] j) := by
  have h : ∀ r j, EvenCatalogue.generatorIndex (rowNumber r) j =
      rowIndex r (![1,2,0,0,0,0] j) := by decide +kernel
  rw [h]
  rfl

theorem rowElement_mem (r : Fin 3) (j : Fin 4) :
    rowElement r j ∈ EvenCatalogue.ambient (rowNumber r) := by
  have hg (k : Fin 6) : rowElement r (![1,2,0,0,0,0] k) ∈
      EvenCatalogue.ambient (rowNumber r) := by
    rw [← rowElement_generator]
    exact ⟨_, subset_closure ⟨k, rfl⟩, rfl⟩
  fin_cases j
  · change rowElement r 0 ∈ _
    rw [rowElement_zero]; exact Subgroup.one_mem _
  · exact hg 0
  · exact hg 1
  · have h := (EvenCatalogue.ambient (rowNumber r)).mul_mem (hg 0) (hg 1)
    rw [rowElement_mul] at h
    exact h

theorem mem_ambient_row_iff (r : Fin 3) (g : M24) :
    g ∈ EvenCatalogue.ambient (rowNumber r) ↔ ∃ j, rowElement r j = g := by
  have hle : EvenCatalogue.ambient (rowNumber r) ≤ rowSubgroup r := by
    rw [EvenCatalogue.ambient, map_le_iff_le_comap, EvenCatalogue.subgroup, closure_le]
    rintro _ ⟨j, rfl⟩
    exact ⟨![1,2,0,0,0,0] j, (rowElement_generator r j).symm⟩
  constructor
  · intro hg
    exact hle hg
  · rintro ⟨j, rfl⟩
    exact rowElement_mem r j

theorem rowElement_ne_one (r : Fin 3) (j : Fin 3) :
    rowElement r j.succ ≠ 1 := by
  intro h
  have hpoints : ∀ x, rowPoint r j.succ x = x := by
    intro x
    rw [← rowElement_apply, h]
    rfl
  have hn : ∀ r : Fin 3, ∀ j : Fin 3, ¬ ∀ x, rowPoint r j.succ x = x := by
    decide +kernel
  exact hn r j hpoints

/-- The fixed points of a permutation on the native Witt-design carrier. -/
def fixedPoints (g : M24) : Finset (Fin 24) := Finset.univ.filter (fun x => g.val x = x)

theorem fixedPoints_conj (g a : M24) :
    fixedPoints (g * a * g⁻¹) = g • fixedPoints a := by
  ext x
  rw [← Finset.inv_smul_mem_iff]
  simp only [fixedPoints, Finset.mem_filter, Finset.mem_univ, true_and]
  change g.val (a.val (g.val.symm x)) = x ↔ a.val (g.val.symm x) = g.val.symm x
  exact g.val.eq_symm_apply.symm

def rowFixed (r : Fin 3) (j : Fin 3) : Finset (Fin 24) :=
  Finset.univ.filter (fun x => rowPoint r j.succ x = x)

def rowGeometry (r : Fin 3) : Finset (Finset (Fin 24)) := Finset.univ.image (rowFixed r)

theorem rowFixed_eq (r : Fin 3) (j : Fin 3) : rowFixed r j = fixedPoints (rowElement r j.succ) := by
  simp only [rowFixed, fixedPoints, rowElement_apply]

/-- Every element of the full normalizer permutes the nonidentity fixed-point sets. -/
theorem normalizer_le_geometry (r : Fin 3) :
    normalizer (EvenCatalogue.ambient (rowNumber r) : Set M24) ≤
      MulAction.stabilizer M24 (rowGeometry r) := by
  intro g hg
  apply MulAction.mem_stabilizer_finset'.mpr
  intro A hA
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hA
  have hc := (mem_set_normalizer_iff.mp hg _).mp (rowElement_mem r j.succ)
  obtain ⟨k, hk⟩ := (mem_ambient_row_iff r _).mp hc
  have hkn : k ≠ 0 := by
    intro he
    rw [he, rowElement_zero] at hk
    have ha : rowElement r j.succ = 1 := by
      have hh := congrArg (MulAut.conj g⁻¹) hk
      simpa [MulAut.conj_apply, mul_assoc] using hh.symm
    exact rowElement_ne_one r j ha
  obtain ⟨l, rfl⟩ : ∃ l : Fin 3, l.succ = k := by
    fin_cases k
    · exact (hkn rfl).elim
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  apply Finset.mem_image.mpr
  refine ⟨l, Finset.mem_univ _, ?_⟩
  rw [rowFixed_eq, hk, fixedPoints_conj, rowFixed_eq]

/-- The octad fixed by Sylow element 106, present in both of the first two four-groups. -/
noncomputable def commonOctad : Octad := ⟨m24BlockAt 456,
  Finset.mem_image.mpr ⟨456, Finset.mem_univ _, rfl⟩⟩

private theorem commonOctad_card : commonOctad.val.card = 8 := by decide +kernel

private theorem small_geometry : ∀ r : Fin 3, r ≠ 2 →
    commonOctad.val ∈ rowGeometry r ∧ rowGeometry r ⊆ {commonOctad.val, ∅} := by
  decide +kernel

/-- The first two full normalizers preserve the octad fixed by Sylow element 106. -/
theorem normalizer_le_octad (r : Fin 3) (hr : r ≠ 2) :
    normalizer (EvenCatalogue.ambient (rowNumber r) : Set M24) ≤
      octadStabilizer commonOctad := by
  intro g hg
  have hh := MulAction.mem_stabilizer_finset'.mp (normalizer_le_geometry r hg)
    (small_geometry r hr).1
  have hm := (small_geometry r hr).2 hh
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with h | h
  · exact h
  · have hc := congrArg Finset.card h
    rw [Finset.card_smul_finset, commonOctad_card, Finset.card_empty] at hc
    omega

end Sporadic.Mathieu.M24LocalGeometry.FourNormalizers
