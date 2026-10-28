module

public import CFSG.Quasithin.MainConverse.SporadicLocal.J3.Coverage.Fusion.ClassData
import Mathlib.Tactic.FinCases

/-!
# Reducing elementary fusion to the 28 ambient word calculations

The Sylow conjugators transport the generated index sets. For the ambient
stage it suffices to check the images of the selected generators: the finite
span certificate proves that those images generate the whole Sylow class.
All conjugations are left conjugations in the concrete model.

Source: the computational route to GLS, Number 3, Table 5.3h, printed p.269.
-/

namespace CFSG.Quasithin.MainConverse.SporadicLocal.J3Coverage.Fusion
open Subgroup Sporadic.Janko3 Sporadic.Janko3.TwoLocal

private theorem generated_conj (hS : Nat.card sylowCandidate = 128)
    (s : Finset (Fin 128)) (g : Fin 128) :
    generated (s.image (conjIndex g)) =
      (generated s).map (MulAut.conj (element g)).toMonoidHom := by
  unfold generated
  rw [MonoidHom.map_closure, Finset.coe_image, Set.image_image, Set.image_image]
  congr 1
  apply Set.image_congr
  intro i _
  exact element_conj hS g i

/-- The certified Sylow conjugators give actual subgroup equalities. -/
public theorem catalogueSubgroup_conjugate (hS : Nat.card sylowCandidate = 128)
    (i : Fin 140) :
    catalogueSubgroup i.succ =
      (classSubgroup (catalogueClass i)).map
        (MulAut.conj (element (catalogueConjugator i))).toMonoidHom := by
  unfold catalogueSubgroup classSubgroup
  rw [catalogue_conjugation, generated_conj hS]

private theorem representative_le_of_basis {i : Fin 5} {H : Subgroup Model}
    (h : ∀ j ∈ representativeBasis i, elementaryGenerator j ∈ H) :
    elementaryRepresentative i ≤ H := by
  fin_cases i
  · exact zpowers_le.mpr (elementaryGenerator_zero ▸ h 0 (by decide))
  · exact sup_le (zpowers_le.mpr (h 0 (by decide)))
      (zpowers_le.mpr (h 1 (by decide)))
  · exact sup_le (zpowers_le.mpr (h 0 (by decide)))
      (zpowers_le.mpr (h 2 (by decide)))
  · exact sup_le (sup_le (zpowers_le.mpr (h 1 (by decide)))
      (zpowers_le.mpr (h 2 (by decide)))) (zpowers_le.mpr (h 3 (by decide)))
  · apply (closure_le H).mpr
    rintro _ ⟨j, rfl⟩
    exact h j (by fin_cases j <;> decide)

private theorem basis_mem_representative (i : Fin 5) (j : Fin 4)
    (hj : j ∈ representativeBasis i) :
    elementaryGenerator j ∈ elementaryRepresentative i := by
  fin_cases i
  · change j ∈ [0] at hj
    have hj : j = 0 := List.mem_singleton.mp hj
    subst j
    change elementaryGenerator 0 ∈ zpowers a
    rw [elementaryGenerator_zero]
    exact mem_zpowers a
  · change j ∈ [0, 1] at hj
    have hj : j = 0 ∨ j = 1 := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false] using hj
    rcases hj with rfl | rfl
    · exact mem_sup_left (mem_zpowers _)
    · exact mem_sup_right (mem_zpowers _)
  · change j ∈ [0, 2] at hj
    have hj : j = 0 ∨ j = 2 := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false] using hj
    rcases hj with rfl | rfl
    · exact mem_sup_left (mem_zpowers _)
    · exact mem_sup_right (mem_zpowers _)
  · change j ∈ [1, 2, 3] at hj
    have hj : j = 1 ∨ j = 2 ∨ j = 3 := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false] using hj
    rcases hj with rfl | rfl | rfl
    · exact mem_sup_left (mem_sup_left (mem_zpowers _))
    · exact mem_sup_left (mem_sup_right (mem_zpowers _))
    · exact mem_sup_right (mem_zpowers _)
  · exact elementaryGenerator_mem _

private theorem span_mem (hS : Nat.card sylowCandidate = 128)
    (H : Subgroup Model) (xs : List (Fin 128))
    (hxs : ∀ j ∈ xs, element j ∈ H) : ∀ j ∈ indexSpan xs, element j ∈ H := by
  induction xs with
  | nil =>
    intro j hj
    have hj : j = 0 := by simpa only [indexSpan, List.mem_singleton] using hj
    subst j
    exact element_zero ▸ H.one_mem
  | cons x xs ih =>
    intro j hj
    have hx := hxs x (List.mem_cons_self ..)
    have htail : ∀ k ∈ xs, element k ∈ H := fun k hk => hxs k (List.mem_cons_of_mem _ hk)
    rcases List.mem_append.mp hj with hj | hj
    · exact ih htail j hj
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hj
      rw [element_mul hS]
      exact H.mul_mem hx (ih htail k hk)

/-- Checking only the selected generators discharges the entire ambient
Sylow-class fusion equality. The hypothesis is an actual model identity. -/
public theorem classSubgroup_conjugate_of_generator_images
    (hS : Nat.card sylowCandidate = 128) (c : Fin 28) (g : Model)
    (hconj : ∀ j ∈ representativeBasis (alignedClass c),
      (MulAut.conj g) (elementaryGenerator j) = element (generatorImage c j)) :
    classSubgroup c =
      (elementaryRepresentative (alignedClass c)).map (MulAut.conj g).toMonoidHom := by
  apply le_antisymm
  · apply generated_le
    intro k hk
    rw [class_span, List.mem_toFinset] at hk
    apply span_mem hS _ _ ?_ k hk
    intro j hj
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hj
    exact Subgroup.mem_map.mpr
      ⟨elementaryGenerator l, basis_mem_representative _ l hl, hconj l hl⟩
  · apply (Subgroup.map_le_iff_le_comap).mpr
    apply representative_le_of_basis
    intro j hj
    change (MulAut.conj g) (elementaryGenerator j) ∈ classSubgroup c
    rw [hconj j hj]
    exact element_mem_generated (generatorImage_mem_class c j hj)

end CFSG.Quasithin.MainConverse.SporadicLocal.J3Coverage.Fusion
