module
public import Theory.Mathieu.M24.LocalGeometry.EvenCatalogue.NormalizerOvergroups.Checks
/-!
# Exhaustive native elements of the 22 catalogue subgroups

The checked bit transitions give both directions of enumeration: clearing the
highest bit proves every listed element lies in its generated subgroup, and
closure induction proves every generated element occurs in the list. This is
an enumeration in the native M₂₄ carrier, not in an abstract permutation model.
The fixed-point tables are identified with the same native elements.

Source: GLS3 Table 5.3e; Aschbacher--Smith 15.3.41--42, printed p.1138.
-/
@[expose] public section
namespace Sporadic.Mathieu.M24LocalGeometry.EvenCatalogue.NormalizerOvergroupsProof
open Subgroup SylowNormalizer.OrderEnumeration
set_option maxRecDepth 100000

/-- The three certified base images determine elements of the marked subgroup. -/
theorem candidate_ext (a b : SylowNormalizer.candidate)
    (h : ∀ k : Fin 3, a.val.val (basePoint k) = b.val.val (basePoint k)) : a = b := by
  obtain ⟨i, rfl⟩ := element_surjective a
  obtain ⟨j, rfl⟩ := element_surjective b
  apply congrArg element
  apply (Fin.strictMono_iff_lt_succ.mpr key_lt_succ).injective
  have h0 := h 0
  have h1 := h 1
  have h5 := h 2
  simp only [element_apply] at h0 h1 h5
  change SylowNormalizer.OrderEnumeration.point i 0 = SylowNormalizer.OrderEnumeration.point j 0 at h0
  change SylowNormalizer.OrderEnumeration.point i 1 = SylowNormalizer.OrderEnumeration.point j 1 at h1
  change SylowNormalizer.OrderEnumeration.point i 5 = SylowNormalizer.OrderEnumeration.point j 5 at h5
  simp only [key, h0, h1, h5]

noncomputable def native (c : Fin 144) : SylowNormalizer.candidate :=
  element (elementIndex c)

theorem native_apply (c : Fin 144) (x : Fin 24) : (native c).val.val x = point c x := by
  rw [point_spec]
  exact element_apply _ _

theorem native_injective : Function.Injective native := by
  intro c d h
  have hi := element_injective h
  exact (show Function.Injective elementIndex by decide +kernel) hi

theorem native_generator (i : Fin 22) (a : Fin 6) :
    native (generatorCode i a) = element (generatorIndex i a) := by
  rw [native, generatorCode_spec]

theorem row_step (i : Fin 22) (a : Fin 6) (j : Fin 64) :
    element (generatorIndex i a) * native (rowCode i j) = native (rowCode i (toggle a j)) := by
  apply candidate_ext
  intro b
  change (element (generatorIndex i a)).val.val ((native (rowCode i j)).val.val (basePoint b)) = _
  rw [← native_generator, native_apply, native_apply, native_apply]
  exact step_check i a j b

theorem generator_inv (i : Fin 22) (a : Fin 6) :
    (element (generatorIndex i a))⁻¹ = element (generatorIndex i a) := by
  apply inv_eq_of_mul_eq_one_right
  apply candidate_ext
  intro b
  change (element (generatorIndex i a)).val.val
    ((element (generatorIndex i a)).val.val (basePoint b)) = basePoint b
  rw [← native_generator, native_apply, native_apply]
  have h : ∀ (i : Fin 22) (a : Fin 6) (b : Fin 3),
      point (generatorCode i a) (point (generatorCode i a) (basePoint b)) = basePoint b := by
    decide +kernel
  exact h i a b

theorem row_zero (i : Fin 22) : native (rowCode i 0) = 1 := by
  have h : ∀ i : Fin 22, elementIndex (rowCode i 0) = 0 := by decide +kernel
  rw [native, h, Coverage.element_zero]

def lowerMask (j : Fin 64) : Fin 64 :=
  ⟨(j.val - 2 ^ Nat.log2 j.val) % 64, Nat.mod_lt _ (by decide)⟩

def lastBit (j : Fin 64) : Fin 6 :=
  ⟨Nat.log2 j.val % 6, Nat.mod_lt _ (by decide)⟩

private theorem lower_check : ∀ j : Fin 64, j ≠ 0 →
    lowerMask j < j ∧ toggle (lastBit j) (lowerMask j) = j := by decide +kernel

theorem row_mem (i : Fin 22) (j : Fin 64) : native (rowCode i j) ∈ subgroup i := by
  induction j using WellFoundedLT.induction with
  | ind j ih =>
    by_cases hj : j = 0
    · subst j
      rw [row_zero]
      exact (subgroup i).one_mem
    · obtain ⟨hlt, he⟩ := lower_check j hj
      have hm := (subgroup i).mul_mem (Coverage.generator_mem i (lastBit j))
        (ih (lowerMask j) hlt)
      rw [row_step, he] at hm
      exact hm

theorem mem_subgroup_iff (i : Fin 22) (a : SylowNormalizer.candidate) :
    a ∈ subgroup i ↔ ∃ j : Fin 64, native (rowCode i j) = a := by
  constructor
  · intro ha
    apply closure_induction_left (s := Set.range (fun a => element (generatorIndex i a)))
      (p := fun a _ => ∃ j, native (rowCode i j) = a) ?_ ?_ ?_ ha
    · exact ⟨0, row_zero i⟩
    · rintro _ ⟨a, rfl⟩ _ _ ⟨j, rfl⟩
      exact ⟨toggle a j, (row_step i a j).symm⟩
    · rintro _ ⟨a, rfl⟩ _ _ ⟨j, rfl⟩
      rw [generator_inv]
      exact ⟨toggle a j, (row_step i a j).symm⟩
  · rintro ⟨j, rfl⟩
    exact row_mem i j

noncomputable def rowElement (i : Fin 22) (j : Fin 64) : M24 := (native (rowCode i j)).val

theorem rowElement_apply (i : Fin 22) (j : Fin 64) (x : Fin 24) :
    (rowElement i j).val x = point (rowCode i j) x := native_apply _ _

theorem rowElement_mem (i : Fin 22) (j : Fin 64) : rowElement i j ∈ ambient i :=
  ⟨_, row_mem i j, rfl⟩

theorem mem_ambient_iff (i : Fin 22) (a : M24) :
    a ∈ ambient i ↔ ∃ j : Fin 64, rowElement i j = a := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨j, rfl⟩ := (mem_subgroup_iff i a).mp ha
    exact ⟨j, rfl⟩
  · rintro ⟨j, rfl⟩
    exact rowElement_mem i j

theorem rowElement_eq_iff (i : Fin 22) (j k : Fin 64) :
    rowElement i j = rowElement i k ↔ rowCode i j = rowCode i k := by
  constructor
  · intro h
    exact native_injective (Subtype.ext h)
  · intro h
    exact congrArg (fun c => (native c).val) h

/-- Fixed points in the native permutation action. -/
def fixedPoints (a : M24) : Finset (Fin 24) := Finset.univ.filter (fun x => a.val x = x)

theorem fixedPoints_row (i : Fin 22) (j : Fin 64) :
    fixedPoints (rowElement i j) = fixedSet (fixedClass (rowCode i j)) := by
  ext x
  simp only [fixedPoints, Finset.mem_filter, Finset.mem_univ, true_and, rowElement_apply]
  exact (show ∀ (c : Fin 144) (x : Fin 24),
    point c x = x ↔ x ∈ fixedSet (fixedClass c) by decide +kernel) _ _

theorem fixedSet_injective : Function.Injective fixedSet := by decide +kernel

end Sporadic.Mathieu.M24LocalGeometry.EvenCatalogue.NormalizerOvergroupsProof
