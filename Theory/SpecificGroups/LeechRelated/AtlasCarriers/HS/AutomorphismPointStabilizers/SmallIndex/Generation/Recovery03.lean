module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers.SmallIndex.Generation.Support

/-!
# Conjugate-pair recovery words, part 4

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

theorem recover_032 : pairSubgroup 32 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 32 [2, 0, 3, 1, 1, 3, 3, 1, 1, 3, 0, 0, 0, 2, 0, 0, 3, 1, 3, 1, 2] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 32 [2, 0, 3, 1, 1, 3, 3, 1, 1, 3, 0, 0, 0, 2, 0, 0, 3, 1, 3, 1, 2]
  · have h : pairWord 32 [1, 3, 3, 3, 0, 2, 2, 0, 2, 2, 0, 3, 1, 3, 1, 2, 0, 0, 0] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 32 [1, 3, 3, 3, 0, 2, 2, 0, 2, 2, 0, 3, 1, 3, 1, 2, 0, 0, 0]

theorem recover_033 : pairSubgroup 33 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 33 [3, 0, 3, 0, 2, 1, 3, 0, 0, 2, 2, 0, 2, 1, 1, 3, 3, 3, 1, 3, 1, 3, 0, 2, 0, 3, 1] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 33 [3, 0, 3, 0, 2, 1, 3, 0, 0, 2, 2, 0, 2, 1, 1, 3, 3, 3, 1, 3, 1, 3, 0, 2, 0, 3, 1]
  · have h : pairWord 33 [0, 2, 1, 3, 1, 3, 0, 0, 0, 0, 3, 1, 2, 1, 3, 3, 0, 0, 0, 2, 2, 2] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 33 [0, 2, 1, 3, 1, 3, 0, 0, 0, 0, 3, 1, 2, 1, 3, 3, 0, 0, 0, 2, 2, 2]

theorem recover_034 : pairSubgroup 34 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 34 [2, 2, 2, 1, 1, 1, 1, 3, 0, 2, 2, 0, 2, 2, 0, 0, 3, 0, 3, 0, 3, 1, 3, 0, 3, 0, 2, 2] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 34 [2, 2, 2, 1, 1, 1, 1, 3, 0, 2, 2, 0, 2, 2, 0, 0, 3, 0, 3, 0, 3, 1, 3, 0, 3, 0, 2, 2]
  · have h : pairWord 34 [1, 2, 1, 2, 0, 3, 3, 0, 2, 2, 2, 0, 2, 0, 3, 3, 3, 1] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 34 [1, 2, 1, 2, 0, 3, 3, 0, 2, 2, 2, 0, 2, 0, 3, 3, 3, 1]

theorem recover_035 : pairSubgroup 35 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 35 [1, 3, 0, 0, 3, 1, 1, 3, 0, 0, 0, 3, 0, 3, 0, 0, 3, 0, 2, 0, 2] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 35 [1, 3, 0, 0, 3, 1, 1, 3, 0, 0, 0, 3, 0, 3, 0, 0, 3, 0, 2, 0, 2]
  · have h : pairWord 35 [0, 2, 0, 3, 1, 3, 1, 2, 1, 2, 0, 3, 0, 3, 0, 0, 3, 0, 2, 1, 1, 1, 1, 2, 2, 0, 3, 0, 0] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 35 [0, 2, 0, 3, 1, 3, 1, 2, 1, 2, 0, 3, 0, 3, 0, 0, 3, 0, 2, 1, 1, 1, 1, 2, 2, 0, 3, 0, 0]

theorem recover_036 : pairSubgroup 36 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 36 [1, 1, 2, 2, 0, 2, 0, 3, 1, 3, 0, 3, 1, 1, 3, 3, 3, 1, 3, 3, 3, 0, 2, 2, 2, 0, 3, 3, 1, 1, 3] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 36 [1, 1, 2, 2, 0, 2, 0, 3, 1, 3, 0, 3, 1, 1, 3, 3, 3, 1, 3, 3, 3, 0, 2, 2, 2, 0, 3, 3, 1, 1, 3]
  · have h : pairWord 36 [0, 2, 0, 3, 0, 3, 3, 3, 1, 1, 1, 1, 1, 1, 3, 0, 3, 3] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 36 [0, 2, 0, 3, 0, 3, 3, 3, 1, 1, 1, 1, 1, 1, 3, 0, 3, 3]

theorem recover_037 : pairSubgroup 37 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 37 [2, 1, 3, 1, 1, 3, 1, 1, 1, 2, 2, 2, 0, 2, 1, 3] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 37 [2, 1, 3, 1, 1, 3, 1, 1, 1, 2, 2, 2, 0, 2, 1, 3]
  · have h : pairWord 37 [1, 3, 0, 2, 0, 3, 0, 2, 0, 3, 1, 3, 1, 3, 0, 2, 0, 2, 0, 3, 3, 0, 3, 3, 0, 2] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 37 [1, 3, 0, 2, 0, 3, 0, 2, 0, 3, 1, 3, 1, 3, 0, 2, 0, 2, 0, 3, 3, 0, 3, 3, 0, 2]

theorem recover_038 : pairSubgroup 38 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 38 [2, 2, 0, 3, 0, 0, 2, 0, 0, 0, 3, 0, 0, 2, 2, 2, 1, 1, 3, 1, 2, 2, 0, 3, 0, 0] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 38 [2, 2, 0, 3, 0, 0, 2, 0, 0, 0, 3, 0, 0, 2, 2, 2, 1, 1, 3, 1, 2, 2, 0, 3, 0, 0]
  · have h : pairWord 38 [3, 0, 3, 0, 2, 1, 3, 3, 3, 0, 0, 3, 3, 0, 2, 2, 0, 2, 0, 2, 2] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 38 [3, 0, 3, 0, 2, 1, 3, 3, 3, 0, 0, 3, 3, 0, 2, 2, 0, 2, 0, 2, 2]

theorem recover_039 : pairSubgroup 39 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 39 [1, 2, 0, 2, 1, 1, 2, 0, 2, 0, 3, 1, 1, 1, 3, 0, 0, 3, 1] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 39 [1, 2, 0, 2, 1, 1, 2, 0, 2, 0, 3, 1, 1, 1, 3, 0, 0, 3, 1]
  · have h : pairWord 39 [3, 1, 1, 2, 2, 2, 2, 1, 3, 3, 3, 0, 0, 3, 3, 1] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 39 [3, 1, 1, 2, 2, 2, 2, 1, 3, 3, 3, 0, 0, 3, 3, 1]

theorem recover_040 : pairSubgroup 40 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 40 [2, 1, 1, 3, 3, 0, 0, 3, 1, 3, 0, 2, 1, 2, 0, 0, 3, 0] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 40 [2, 1, 1, 3, 3, 0, 0, 3, 1, 3, 0, 2, 1, 2, 0, 0, 3, 0]
  · have h : pairWord 40 [1, 3, 0, 3, 3, 0, 2, 0, 2, 2, 1, 3, 0, 3, 3, 3, 1] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 40 [1, 3, 0, 3, 3, 0, 2, 0, 2, 2, 1, 3, 0, 3, 3, 3, 1]

theorem recover_041 : pairSubgroup 41 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 41 [1, 2, 0, 0, 2, 0, 3, 3, 3, 3, 3, 1, 2, 0, 0, 0, 0, 3] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 41 [1, 2, 0, 0, 2, 0, 3, 3, 3, 3, 3, 1, 2, 0, 0, 0, 0, 3]
  · have h : pairWord 41 [3, 0, 3, 3, 0, 2, 2, 2, 0, 3, 3, 1, 2] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 41 [3, 0, 3, 3, 0, 2, 2, 2, 0, 3, 3, 1, 2]

end Sporadic.LeechRelated.HS.SmallIndex.GenerationCertificate
