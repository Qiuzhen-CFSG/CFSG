module

public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.GrassmannConditions
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Alternating maps from binary Grassmann assignments

The three geometric conditions in `GrassmannAssignment` imply additivity in
every coordinate, including dependent frames. Fixing the other coordinates,
an update is independent precisely when those coordinates are independent and
the new vector is outside their span. Adding a vector in that span preserves
both independence and the full span, so the dependent cases follow from the
zero and equal-span conditions. The remaining case is the Grassmann-line
relation. Scalars are zero or one, and repeated coordinates are dependent.

This is the multilinear extension step in the exterior presentation used for
Aschbacher--Smith, *The Classification of Quasithin Groups*, Lemma I.1.6(7),
printed p.408/PDF p.419. Constructing the Grassmann assignment from the local
seed is a separate step.
-/

@[expose] public section

open Function

namespace Representation.SL5TenDimensional.Classification

-- Separate the unchanged coordinates from the coordinate being updated.
private theorem update_independent_iff {a : Fin 2} (w : BinaryFrame a)
    (i : Fin (degree a)) (x : BinarySpace) :
    LinearIndependent (ZMod 2) (update w i x) ↔
      LinearIndepOn (ZMod 2) w ({i}ᶜ) ∧
        x ∉ Submodule.span (ZMod 2) (w '' {i}ᶜ) := by
  have heq : Set.EqOn (update w i x) w {i}ᶜ := by
    intro j hj
    exact update_of_ne (by simpa using hj) _ _
  have hins : insert i ({i}ᶜ : Set (Fin (degree a))) = Set.univ := by
    ext j
    simp only [Set.mem_insert_iff, Set.mem_compl_iff, Set.mem_singleton_iff,
      Set.mem_univ, iff_true]
    exact eq_or_ne j i
  have h := linearIndepOn_insert (K := ZMod 2) (f := update w i x)
    (s := {i}ᶜ) (a := i) (by simp)
  rw [hins, linearIndepOn_univ_iff, linearIndepOn_congr heq,
    Set.image_congr heq, update_self] at h
  exact h

private theorem span_others_le {a : Fin 2} (w : BinaryFrame a)
    (i : Fin (degree a)) (x : BinarySpace) :
    Submodule.span (ZMod 2) (w '' {i}ᶜ) ≤
      Submodule.span (ZMod 2) (Set.range (update w i x)) := by
  apply Submodule.span_mono
  rintro _ ⟨j, hj, rfl⟩
  exact ⟨j, update_of_ne (by simpa using hj) _ _⟩

private theorem span_update_add {a : Fin 2} (w : BinaryFrame a)
    (i : Fin (degree a)) (x y : BinarySpace)
    (hx : x ∈ Submodule.span (ZMod 2) (w '' {i}ᶜ)) :
    Submodule.span (ZMod 2) (Set.range (update w i (x + y))) =
      Submodule.span (ZMod 2) (Set.range (update w i y)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    by_cases hj : j = i
    · subst j
      rw [update_self]
      exact Submodule.add_mem _ (span_others_le w i y hx)
        (Submodule.subset_span ⟨i, update_self _ _ _⟩)
    · exact Submodule.subset_span ⟨j, by simp [hj]⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    by_cases hj : j = i
    · subst j
      rw [update_self]
      have hxy : x + y ∈ Submodule.span (ZMod 2) (Set.range (update w i (x + y))) :=
        Submodule.subset_span ⟨i, update_self _ _ _⟩
      simpa using Submodule.sub_mem _ hxy (span_others_le w i (x + y) hx)
    · exact Submodule.subset_span ⟨j, by simp [hj]⟩

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) Group V} {a : Fin 2} {v : V}

private theorem binary_add_self (z : V) : z + z = 0 := by
  have htwo : (1 : ZMod 2) + 1 = 0 := by decide
  calc
    z + z = ((1 : ZMod 2) + 1) • z := by rw [add_smul, one_smul]
    _ = 0 := by rw [htwo, zero_smul]

-- A dependent first update contributes zero and does not change the second value.
private theorem value_update_add_of_dependent
    (C : GrassmannAssignment ρ a v) (w : BinaryFrame a)
    (i : Fin (degree a)) (x y : BinarySpace)
    (hx : ¬LinearIndependent (ZMod 2) (update w i x)) :
    C.value (update w i (x + y)) = C.value (update w i y) := by
  by_cases hw : LinearIndepOn (ZMod 2) w {i}ᶜ
  · have hxmem : x ∈ Submodule.span (ZMod 2) (w '' {i}ᶜ) := by
      by_contra h
      exact hx ((update_independent_iff w i x).mpr ⟨hw, h⟩)
    have hmem : x + y ∈ Submodule.span (ZMod 2) (w '' {i}ᶜ) ↔
        y ∈ Submodule.span (ZMod 2) (w '' {i}ᶜ) :=
      Submodule.add_mem_iff_right _ hxmem
    by_cases hy : LinearIndependent (ZMod 2) (update w i y)
    · apply C.equal_span _ _ ?_ hy (span_update_add w i x y hxmem)
      exact (update_independent_iff w i (x + y)).mpr
        ⟨hw, fun h => (update_independent_iff w i y).mp hy |>.2 (hmem.mp h)⟩
    · rw [C.zero_dependent _ hy, C.zero_dependent _ ?_]
      intro hxy
      apply hy
      exact (update_independent_iff w i y).mpr
        ⟨hw, fun h => (update_independent_iff w i (x + y)).mp hxy |>.2 (hmem.mpr h)⟩
  · have hd (z : BinarySpace) : ¬LinearIndependent (ZMod 2) (update w i z) :=
      fun h => hw ((update_independent_iff w i z).mp h).1
    rw [C.zero_dependent _ (hd (x + y)), C.zero_dependent _ (hd y)]

private theorem value_update_add (C : GrassmannAssignment ρ a v)
    (w : BinaryFrame a) (i : Fin (degree a)) (x y : BinarySpace) :
    C.value (update w i (x + y)) =
      C.value (update w i x) + C.value (update w i y) := by
  by_cases hx : LinearIndependent (ZMod 2) (update w i x)
  swap
  · rw [value_update_add_of_dependent C w i x y hx, C.zero_dependent _ hx, zero_add]
  by_cases hy : LinearIndependent (ZMod 2) (update w i y)
  swap
  · rw [add_comm x y, value_update_add_of_dependent C w i y x hy,
      C.zero_dependent _ hy, add_zero]
  by_cases hxy : LinearIndependent (ZMod 2) (update w i (x + y))
  · have h := C.line w i x y hx hy hxy
    have h' := congrArg (fun z => z + C.value (update w i (x + y))) h
    simpa only [add_assoc, binary_add_self, add_zero, zero_add] using h'.symm
  · have heq := value_update_add_of_dependent C w i (x + y) y hxy
    have hxyy : x + y + y = x := by rw [add_assoc, binary_add_self, add_zero]
    rw [hxyy] at heq
    rw [C.zero_dependent _ hxy, heq, binary_add_self]

/-- Every binary Grassmann assignment is the evaluation function of an alternating
map, with no further assumptions on its dependent frames. -/
theorem GrassmannAssignment.exists_alternatingMap (C : GrassmannAssignment ρ a v) :
    ∃ A : BinarySpace [⋀^Fin (degree a)]→ₗ[ZMod 2] V,
      ∀ w : BinaryFrame a, A w = C.value w := by
  refine ⟨{
    toFun := C.value
    map_update_add' := ?_
    map_update_smul' := ?_
    map_eq_zero_of_eq' := ?_
  }, fun _ => rfl⟩
  · intro inst w i x y
    cases Subsingleton.elim inst (instDecidableEqFin (degree a))
    exact value_update_add C w i x y
  · intro _ w i c x
    have hc : c = (0 : ZMod 2) ∨ c = 1 := by
      fin_cases c
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hc with rfl | rfl
    · simp only [zero_smul]
      apply C.zero_dependent
      intro h
      exact h.ne_zero i (update_self _ _ _)
    · simp
  · intro w i j hij hne
    exact C.zero_dependent w (fun h => hne (h.injective hij))

end Representation.SL5TenDimensional.Classification
