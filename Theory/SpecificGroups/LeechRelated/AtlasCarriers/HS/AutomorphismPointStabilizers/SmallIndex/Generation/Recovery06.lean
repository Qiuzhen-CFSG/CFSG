module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers.SmallIndex.Generation.Support

/-!
# Conjugate-pair recovery words, part 7

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

theorem recover_062 : pairSubgroup 62 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 62 [2, 0, 3, 3, 3, 3, 3, 1, 1, 1, 2, 0, 3, 0, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 62 [2, 0, 3, 3, 3, 3, 3, 1, 1, 1, 2, 0, 3, 0, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2]
  · have h : pairWord 62 [3, 3, 1, 1, 3, 0, 2, 1, 1, 2, 0, 3, 3, 3, 3, 3, 1, 1, 1, 2] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 62 [3, 3, 1, 1, 3, 0, 2, 1, 1, 2, 0, 3, 3, 3, 3, 3, 1, 1, 1, 2]

theorem recover_063 : pairSubgroup 63 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 63 [1, 3, 3, 1, 3, 1, 2, 0, 3, 1, 3, 1, 3, 3, 1, 2, 1, 2, 0, 2, 0] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 63 [1, 3, 3, 1, 3, 1, 2, 0, 3, 1, 3, 1, 3, 3, 1, 2, 1, 2, 0, 2, 0]
  · have h : pairWord 63 [1, 3, 3, 1, 2, 2, 0, 3, 1, 2, 2, 2, 2, 2, 1] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 63 [1, 3, 3, 1, 2, 2, 0, 3, 1, 2, 2, 2, 2, 2, 1]

theorem recover_064 : pairSubgroup 64 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 64 [3, 0, 0, 3, 1, 3, 0, 0, 0, 0, 2, 2, 0, 2, 1, 1] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 64 [3, 0, 0, 3, 1, 3, 0, 0, 0, 0, 2, 2, 0, 2, 1, 1]
  · have h : pairWord 64 [3, 3, 0, 3, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 1, 3, 3, 1] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 64 [3, 3, 0, 3, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 1, 3, 3, 1]

theorem recover_065 : pairSubgroup 65 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 65 [0, 0, 2, 2, 2, 0, 3, 1, 3, 1, 1, 2, 2, 2, 1, 3, 0, 2, 2, 2] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 65 [0, 0, 2, 2, 2, 0, 3, 1, 3, 1, 1, 2, 2, 2, 1, 3, 0, 2, 2, 2]
  · have h : pairWord 65 [3, 1, 1, 2, 1, 2, 1, 3, 0, 3, 1, 3, 0, 0, 2, 2, 1, 3, 0] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 65 [3, 1, 1, 2, 1, 2, 1, 3, 0, 3, 1, 3, 0, 0, 2, 2, 1, 3, 0]

theorem recover_066 : pairSubgroup 66 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 66 [3, 0, 0, 2, 2, 0, 2, 2, 2, 2, 2, 1, 1, 1, 1, 3, 0, 2, 2, 2, 0, 2, 1, 2, 0] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 66 [3, 0, 0, 2, 2, 0, 2, 2, 2, 2, 2, 1, 1, 1, 1, 3, 0, 2, 2, 2, 0, 2, 1, 2, 0]
  · have h : pairWord 66 [3, 0, 0, 2, 2, 0, 3, 1, 3, 3, 0, 3, 1, 2, 1, 3, 1, 3, 1, 1, 1, 3, 3, 3] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 66 [3, 0, 0, 2, 2, 0, 3, 1, 3, 3, 0, 3, 1, 2, 1, 3, 1, 3, 1, 1, 1, 3, 3, 3]

theorem recover_067 : pairSubgroup 67 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 67 [2, 2, 0, 2, 1, 1, 3, 0, 2, 2, 2, 0, 2, 1, 3, 0, 0, 2, 0, 0, 2, 1, 1] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 67 [2, 2, 0, 2, 1, 1, 3, 0, 2, 2, 2, 0, 2, 1, 3, 0, 0, 2, 0, 0, 2, 1, 1]
  · have h : pairWord 67 [2, 0, 2, 2, 1, 3, 1, 2, 2, 1, 1, 1, 3, 3, 0, 0, 3, 1, 2, 1] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 67 [2, 0, 2, 2, 1, 3, 1, 2, 2, 1, 1, 1, 3, 3, 0, 0, 3, 1, 2, 1]

theorem recover_068 : pairSubgroup 68 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 68 [1, 1, 1, 2, 2, 2, 0, 0, 3, 1, 3, 0, 3, 3, 3, 0, 0, 3, 1] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 68 [1, 1, 1, 2, 2, 2, 0, 0, 3, 1, 3, 0, 3, 3, 3, 0, 0, 3, 1]
  · have h : pairWord 68 [2, 2, 0, 2, 0, 0, 2, 0, 2, 0, 3, 0, 3, 1, 2, 2, 1, 1, 3, 3, 3, 1] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 68 [2, 2, 0, 2, 0, 0, 2, 0, 2, 0, 3, 0, 3, 1, 2, 2, 1, 1, 3, 3, 3, 1]

theorem recover_069 : pairSubgroup 69 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 69 [1, 1, 3, 0, 3, 3, 3, 1, 3, 0, 3, 1, 2, 2, 1, 1, 3, 0, 2, 0, 3, 0, 3, 1, 3, 0, 3, 1] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 69 [1, 1, 3, 0, 3, 3, 3, 1, 3, 0, 3, 1, 2, 2, 1, 1, 3, 0, 2, 0, 3, 0, 3, 1, 3, 0, 3, 1]
  · have h : pairWord 69 [0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 3, 0, 3, 1, 1, 2, 0] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 69 [0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 3, 0, 3, 1, 1, 2, 0]

theorem recover_070 : pairSubgroup 70 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 70 [0, 3, 1, 3, 3, 3, 0, 2, 1, 1, 1, 1, 1, 3, 3, 3, 0, 0, 0, 0, 3, 1, 3, 3, 3, 1, 2, 0, 3, 1] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 70 [0, 3, 1, 3, 3, 3, 0, 2, 1, 1, 1, 1, 1, 3, 3, 3, 0, 0, 0, 0, 3, 1, 3, 3, 3, 1, 2, 0, 3, 1]
  · have h : pairWord 70 [3, 1, 2, 2, 0, 3, 1, 1, 1, 3, 1, 2, 2, 1, 3, 0, 2, 0, 2] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 70 [3, 1, 2, 2, 0, 3, 1, 1, 1, 3, 1, 2, 2, 1, 3, 0, 2, 0, 2]

theorem recover_071 : pairSubgroup 71 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 71 [2, 1, 1, 1, 3, 0, 2, 2, 1, 1, 2, 0, 3, 3, 3, 3, 1, 2, 1, 3, 0, 2, 1] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 71 [2, 1, 1, 1, 3, 0, 2, 2, 1, 1, 2, 0, 3, 3, 3, 3, 1, 2, 1, 3, 0, 2, 1]
  · have h : pairWord 71 [1, 1, 1, 3, 0, 0, 3, 0, 2, 0, 0, 3, 3, 0, 3, 1, 3, 0, 2, 2, 2] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 71 [1, 1, 1, 3, 0, 0, 3, 0, 2, 0, 0, 3, 3, 0, 3, 1, 3, 0, 2, 2, 2]

end Sporadic.LeechRelated.HS.SmallIndex.GenerationCertificate
