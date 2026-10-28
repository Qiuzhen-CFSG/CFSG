module

public import Theory.SpecificGroups.PSL3Four.MathieuAmalgamMarking.Matrices
import all Theory.SpecificGroups.PSL3Four.MathieuAmalgamMarking.Matrices

/-!
# The four hexad words on the shared canonical pair

These four words involve only the two shared generators. Their values are
checked on the literal determinant-one matrices over the existing field of
four elements, then projected to the original canonical PSL group. Both
exterior generators remain arbitrary, including after homomorphic transport.
-/

public noncomputable section
open Subgroup Subgroup.CosetWordCertificate Matrix
namespace Matrix.PSL3Four.MathieuAmalgamMarking
open Theory.SpecificGroups.MathieuAmalgamCompletion

private theorem shared_support : ∀ i : Fin 27,
    i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 23 →
    ∀ a ∈ relator i, a.1 = 0 ∨ a.1 = 1 := by decide +kernel

private theorem shared_native_relators : ∀ i : Fin 27,
    i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 23 →
    ∃ a : NativeF, a ^ 3 = 1 ∧ scalar (Fin 3) a =
      (eval nativeGenerator (relator i)).val := by decide +kernel

private theorem shared_eval_agrees {G α : Type*} [Group G]
    (g h : α → G) (v : Word α)
    (ha : ∀ a ∈ v, g a.1 = h a.1) : eval g v = eval h v := by
  induction v with
  | nil => simp
  | cons a v ih =>
    rw [eval_cons, eval_cons, ha a (by simp),
      ih (fun b hb => ha b (by simp [hb]))]

/-- All four hexad relators supported on the shared pair hold independently
of the two exterior generator values. -/
theorem shared_hexad_relators (ell n : PSL) (i : Fin 27)
    (hi : i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 23) :
    eval ![pair 0, pair 1, ell, n] (relator i) = 1 := by
  have he : eval ![pair 0, pair 1, ell, n] (relator i) =
      eval generator (relator i) := by
    apply shared_eval_agrees
    intro a ha
    rcases shared_support i hi a ha with h | h <;> rw [h] <;> rfl
  rw [he]
  change eval (fun j => project (nativeGenerator j)) _ = 1
  rw [← map_eval project nativeGenerator]
  obtain ⟨a, ha, hg⟩ := shared_native_relators i hi
  exact project_scalar _ a ha hg

/-- Homomorphic transport retains the same shared pair and permits arbitrary
exterior elements in the original ambient group. -/
theorem mapped_shared_hexad_relators {G : Type*} [Group G]
    (f : PSL →* G) (ell n : G) (i : Fin 27)
    (hi : i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 23) :
    eval ![f (pair 0), f (pair 1), ell, n] (relator i) = 1 := by
  have he : eval ![f (pair 0), f (pair 1), ell, n] (relator i) =
      eval (fun j => f (![pair 0, pair 1, 1, 1] j)) (relator i) := by
    apply shared_eval_agrees
    intro a ha
    rcases shared_support i hi a ha with h | h <;> rw [h] <;> rfl
  rw [he, ← map_eval, shared_hexad_relators 1 1 i hi, map_one]

end Matrix.PSL3Four.MathieuAmalgamMarking
