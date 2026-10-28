module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers.SmallIndex.Generation.Support

/-!
# Conjugate-pair recovery words, part 3

Each pair recovers the two generators of the certified stabilizer.
The displayed words are checked as permutations on all 100 letters by
Lean's kernel. Source context: GLS3 Table 5.3m, p.274; the original CFSG
witness discovery is retained in `Generation/source/`.
-/

public section
namespace Sporadic.LeechRelated.HS.SmallIndex.GenerationCertificate
open Theory.GroupTheory
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

theorem recover_022 : pairSubgroup 22 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 22 [0, 0, 0, 0, 3, 3, 0, 3, 0, 3, 3, 1, 1, 2, 2, 1] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 22 [0, 0, 0, 0, 3, 3, 0, 3, 0, 3, 3, 1, 1, 2, 2, 1]
  · have h : pairWord 22 [0, 0, 0, 0, 3, 1, 2, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 3, 1] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 22 [0, 0, 0, 0, 3, 1, 2, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 3, 1]

theorem recover_023 : pairSubgroup 23 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 23 [0, 3, 3, 1, 3, 3, 0, 2, 1, 2, 2, 1, 3, 1, 1, 3, 0, 2, 0, 0, 0, 3, 3, 1, 2, 1, 2, 0, 2, 0, 2, 0] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 23 [0, 3, 3, 1, 3, 3, 0, 2, 1, 2, 2, 1, 3, 1, 1, 3, 0, 2, 0, 0, 0, 3, 3, 1, 2, 1, 2, 0, 2, 0, 2, 0]
  · have h : pairWord 23 [2, 0, 3, 1, 2, 2, 2, 2, 0, 0, 2, 0, 0, 0, 3] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 23 [2, 0, 3, 1, 2, 2, 2, 2, 0, 0, 2, 0, 0, 0, 3]

theorem recover_024 : pairSubgroup 24 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 24 [2, 2, 0, 0, 2, 1, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 1, 2, 1, 3] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 24 [2, 2, 0, 0, 2, 1, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 1, 2, 1, 3]
  · have h : pairWord 24 [0, 2, 0, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 3, 0, 0, 0, 3, 3, 1] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 24 [0, 2, 0, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 3, 0, 0, 0, 3, 3, 1]

theorem recover_025 : pairSubgroup 25 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 25 [3, 3, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3, 0, 0, 0, 2, 2, 1, 1, 2] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 25 [3, 3, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3, 0, 0, 0, 2, 2, 1, 1, 2]
  · have h : pairWord 25 [3, 3, 1, 1, 1, 3, 1, 3, 0, 3, 0, 0, 2, 2, 2, 2, 0, 3, 3, 3, 0, 0, 3, 1, 2] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 25 [3, 3, 1, 1, 1, 3, 1, 3, 0, 3, 0, 0, 2, 2, 2, 2, 0, 3, 3, 3, 0, 0, 3, 1, 2]

theorem recover_026 : pairSubgroup 26 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 26 [2, 0, 3, 1, 1, 3, 0, 2, 0, 0, 0] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 26 [2, 0, 3, 1, 1, 3, 0, 2, 0, 0, 0]
  · have h : pairWord 26 [2, 2, 1, 2, 0, 0, 3, 3, 3, 0, 2, 1, 3, 3, 0, 2, 1, 3, 0, 2, 1, 1, 2] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 26 [2, 2, 1, 2, 0, 0, 3, 3, 3, 0, 2, 1, 3, 3, 0, 2, 1, 3, 0, 2, 1, 1, 2]

theorem recover_027 : pairSubgroup 27 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 27 [0, 2, 0, 2, 2, 0, 2, 1, 2, 2, 1, 1, 2, 0, 0, 2] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 27 [0, 2, 0, 2, 2, 0, 2, 1, 2, 2, 1, 1, 2, 0, 0, 2]
  · have h : pairWord 27 [2, 1, 1, 3, 3, 0, 0, 0, 0, 2, 1, 1, 3, 1, 3, 0, 2, 2, 2, 2] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 27 [2, 1, 1, 3, 3, 0, 0, 0, 0, 2, 1, 1, 3, 1, 3, 0, 2, 2, 2, 2]

theorem recover_028 : pairSubgroup 28 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 28 [0, 0, 2, 1, 2, 0, 3, 0, 3, 0, 2, 1, 2, 1, 3, 0, 3, 3, 1, 1] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 28 [0, 0, 2, 1, 2, 0, 3, 0, 3, 0, 2, 1, 2, 1, 3, 0, 3, 3, 1, 1]
  · have h : pairWord 28 [2, 0, 0, 0, 0, 3, 0, 0, 2, 0, 3, 1, 1, 1, 1, 2, 0, 0, 0, 0, 0, 0, 2, 0, 3, 3, 0] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 28 [2, 0, 0, 0, 0, 3, 0, 0, 2, 0, 3, 1, 1, 1, 1, 2, 0, 0, 0, 0, 0, 0, 2, 0, 3, 3, 0]

theorem recover_029 : pairSubgroup 29 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 29 [0, 2, 1, 3, 1, 3, 3, 3, 0, 0, 0, 3, 3, 3, 3, 1, 2, 1, 2] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 29 [0, 2, 1, 3, 1, 3, 3, 3, 0, 0, 0, 3, 3, 3, 3, 1, 2, 1, 2]
  · have h : pairWord 29 [1, 2, 0, 2, 0, 3, 1, 2, 0, 0, 3, 3, 1, 1, 3, 1, 3, 1] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 29 [1, 2, 0, 2, 0, 3, 1, 2, 0, 0, 3, 3, 1, 1, 3, 1, 3, 1]

theorem recover_030 : pairSubgroup 30 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 30 [0, 3, 1, 2, 1, 1, 3, 0, 2, 2, 2, 2, 2, 2, 1, 2, 1, 1, 2, 0, 0, 0] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 30 [0, 3, 1, 2, 1, 1, 3, 0, 2, 2, 2, 2, 2, 2, 1, 2, 1, 1, 2, 0, 0, 0]
  · have h : pairWord 30 [2, 2, 2, 0, 2, 1, 3, 0, 0, 2, 0, 0, 3, 3, 0, 3, 3, 0, 2, 2, 2, 0, 0, 0, 2] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 30 [2, 2, 2, 0, 2, 1, 3, 0, 0, 2, 0, 0, 3, 3, 0, 3, 3, 0, 2, 2, 2, 0, 0, 0, 2]

theorem recover_031 : pairSubgroup 31 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 31 [0, 0, 3, 3, 0, 3, 3, 1, 2, 2, 2, 1, 2, 1, 2, 1, 3, 3, 3, 1, 1] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 31 [0, 0, 3, 3, 0, 3, 3, 1, 2, 2, 2, 1, 2, 1, 2, 1, 3, 3, 3, 1, 1]
  · have h : pairWord 31 [0, 0, 3, 3, 3, 1, 3, 1, 2, 2, 1, 3, 1, 2, 2, 1, 3, 0, 2] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 31 [0, 0, 3, 3, 3, 1, 3, 1, 2, 2, 1, 3, 1, 2, 2, 1, 3, 0, 2]

end Sporadic.LeechRelated.HS.SmallIndex.GenerationCertificate
