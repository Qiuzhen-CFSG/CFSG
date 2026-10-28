module

public import Theory.SpecificGroups.SU3.BorelTorus.FieldActors
public import Theory.SpecificGroups.SU3.ProjectiveGraphFixed

/-!
# The actual graph automorphism on the full unitary torus

Entrywise Hermitian conjugation sends the torus matrix with parameter `u`
to the one with parameter `conj u`, in both SU₃ and its genuine projective
image. Surjective residual transport identifies the three-residual of each
matrix torus. The constructed graph automorphism fixes it pointwise exactly
when the fixed field has order eight (for `n > 1`).

Source: Aschbacher–Smith, proof of 13.8.20, printed p.954. This treats the
constructed graph actor; arbitrary Borel-stabilizing automorphisms still
require the semilinear normalizer calculation.
-/

public section

open Matrix BenderSuzuki.External Subgroup
namespace BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus
variable {E : Type*} [Field E] (J : HermitianForm 3 E)
variable (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

theorem special_graph_torus (u : Eˣ) :
    specialGraphAut J hJ (hermitianTorusSU J hJ u) =
      hermitianTorusSU J hJ (Units.map J.conj.toMonoidHom u) := by
  apply Subtype.ext
  apply Units.ext
  rw [specialGraphAut_apply_val]
  change (hermitianTorusMatrix J u).map J.conj =
    hermitianTorusMatrix J (Units.map J.conj.toMonoidHom u)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermitianTorusMatrix]

theorem specialToProjective_torus (u : Eˣ) :
    J.specialToProjective (hermitianTorusSU J hJ u) = hermitianTorusPSU J hJ u := by
  apply Subtype.ext
  rw [specialToProjective_apply_val, hermitianTorusPSU_val]
  rfl

theorem projective_graph_torus (u : Eˣ) :
    projectiveGraphAut J hJ (hermitianTorusPSU J hJ u) =
      hermitianTorusPSU J hJ (Units.map J.conj.toMonoidHom u) := by
  rw [← specialToProjective_torus, projectiveGraphAut_specialToProjective,
    special_graph_torus, specialToProjective_torus]

variable [Finite E]

theorem special_residual_map :
    (pResidual 3 Eˣ).map (hermitianTorusSU J hJ) =
      (pResidual 3 (specialTorus J hJ)).map (specialTorus J hJ).subtype := by
  unfold specialTorus
  rw [← map_pResidual_of_surjective 3 (hermitianTorusSU J hJ).rangeRestrict
    (hermitianTorusSU J hJ).rangeRestrict_surjective, Subgroup.map_map]
  rfl

theorem projective_residual_map :
    (pResidual 3 Eˣ).map (hermitianTorusPSU J hJ) =
      (pResidual 3 (projectiveTorus J hJ)).map (projectiveTorus J hJ).subtype := by
  unfold projectiveTorus
  rw [← map_pResidual_of_surjective 3 (hermitianTorusPSU J hJ).rangeRestrict
    (hermitianTorusPSU J hJ).rangeRestrict_surjective, Subgroup.map_map]
  rfl

theorem special_graph_fixes_residual_iff
    {n : ℕ} (hn : 1 < n) (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ (2 ^ n)) :
    (∀ t ∈ (pResidual 3 (specialTorus J hJ)).map (specialTorus J hJ).subtype,
      specialGraphAut J hJ t = t) ↔ n = 3 := by
  rw [← special_residual_map, ← special_involution_fixes_iff J hJ hn hcard hconj]
  constructor
  · intro h u hu
    simpa only [special_graph_torus] using h _ (mem_map_of_mem _ hu)
  · intro h t ht
    obtain ⟨u, hu, rfl⟩ := ht
    rw [special_graph_torus, h u hu]

theorem projective_graph_fixes_residual_iff
    {n : ℕ} (hn : 1 < n) (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ (2 ^ n)) :
    (∀ t ∈ (pResidual 3 (projectiveTorus J hJ)).map (projectiveTorus J hJ).subtype,
      projectiveGraphAut J hJ t = t) ↔ n = 3 := by
  rw [← projective_residual_map, ← projective_involution_fixes_iff J hJ hn hcard hconj]
  constructor
  · intro h u hu
    simpa only [projective_graph_torus] using h _ (mem_map_of_mem _ hu)
  · intro h t ht
    obtain ⟨u, hu, rfl⟩ := ht
    rw [projective_graph_torus, h u hu]

end BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus
