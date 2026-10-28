module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers.SmallIndex.Generation.Support

/-!
# Conjugate-pair recovery words, part 6

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

theorem recover_052 : pairSubgroup 52 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 52 [0, 0, 2, 2, 1, 2, 2, 1, 3, 0, 0, 0, 3, 3, 3] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 52 [0, 0, 2, 2, 1, 2, 2, 1, 3, 0, 0, 0, 3, 3, 3]
  · have h : pairWord 52 [2, 0, 3, 3, 3, 3, 0, 3, 3, 0, 2, 0, 3, 0, 0, 0, 0, 2, 2, 0, 0, 2, 2, 2, 2] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 52 [2, 0, 3, 3, 3, 3, 0, 3, 3, 0, 2, 0, 3, 0, 0, 0, 0, 2, 2, 0, 0, 2, 2, 2, 2]

theorem recover_053 : pairSubgroup 53 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 53 [1, 1, 3, 3, 0, 3, 1, 1, 1, 3, 3, 1, 1, 3, 0, 0, 2, 2, 2, 0, 3, 0, 2, 2, 0, 0, 3, 1, 1] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 53 [1, 1, 3, 3, 0, 3, 1, 1, 1, 3, 3, 1, 1, 3, 0, 0, 2, 2, 2, 0, 3, 0, 2, 2, 0, 0, 3, 1, 1]
  · have h : pairWord 53 [1, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 3, 0, 3, 3, 0, 3, 1, 2, 0, 0, 3, 3] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 53 [1, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 3, 0, 3, 3, 0, 3, 1, 2, 0, 0, 3, 3]

theorem recover_054 : pairSubgroup 54 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 54 [2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 2, 2, 0, 0, 0, 0, 2, 2, 1] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 54 [2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 2, 2, 0, 0, 0, 0, 2, 2, 1]
  · have h : pairWord 54 [1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 2, 1, 3] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 54 [1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 2, 1, 3]

theorem recover_055 : pairSubgroup 55 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 55 [0, 0, 3, 3, 3, 3, 1, 3, 1, 2, 1, 1, 3, 1, 1, 1, 2, 0, 0, 0, 2, 1, 3] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 55 [0, 0, 3, 3, 3, 3, 1, 3, 1, 2, 1, 1, 3, 1, 1, 1, 2, 0, 0, 0, 2, 1, 3]
  · have h : pairWord 55 [3, 3, 0, 3, 1, 1, 1, 3, 0, 2, 2, 0, 2, 2, 2, 1, 2] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 55 [3, 3, 0, 3, 1, 1, 1, 3, 0, 2, 2, 0, 2, 2, 2, 1, 2]

theorem recover_056 : pairSubgroup 56 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 56 [0, 0, 0, 3, 0, 2, 1, 2, 2, 2, 0, 3, 3, 0, 3, 1, 1, 3, 1, 1, 1] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 56 [0, 0, 0, 3, 0, 2, 1, 2, 2, 2, 0, 3, 3, 0, 3, 1, 1, 3, 1, 1, 1]
  · have h : pairWord 56 [3, 3, 3, 0, 3, 1, 2, 1, 1, 2, 0, 2, 2, 1, 3, 1, 3] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 56 [3, 3, 3, 0, 3, 1, 2, 1, 1, 2, 0, 2, 2, 1, 3, 1, 3]

theorem recover_057 : pairSubgroup 57 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 57 [0, 3, 1, 3, 1, 3, 3, 1, 1, 3, 0, 3, 1, 3, 3, 1, 1, 1, 3, 0, 3] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 57 [0, 3, 1, 3, 1, 3, 3, 1, 1, 3, 0, 3, 1, 3, 3, 1, 1, 1, 3, 0, 3]
  · have h : pairWord 57 [1, 2, 0, 2, 2, 0, 0, 0, 3, 3, 1, 1, 2, 0, 2, 2, 0, 0, 2, 1, 3, 1, 3] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 57 [1, 2, 0, 2, 2, 0, 0, 0, 3, 3, 1, 1, 2, 0, 2, 2, 0, 0, 2, 1, 3, 1, 3]

theorem recover_058 : pairSubgroup 58 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 58 [3, 0, 3, 0, 2, 1, 2, 2, 2, 0, 3, 1, 1, 1, 2, 0, 0, 3, 3, 1, 1, 2, 1, 2, 1] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 58 [3, 0, 3, 0, 2, 1, 2, 2, 2, 0, 3, 1, 1, 1, 2, 0, 0, 3, 3, 1, 1, 2, 1, 2, 1]
  · have h : pairWord 58 [1, 1, 1, 3, 0, 2, 1, 2, 0, 0, 0, 3, 3, 1, 3, 0, 3, 1, 2, 1, 1, 2, 0] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 58 [1, 1, 1, 3, 0, 2, 1, 2, 0, 0, 0, 3, 3, 1, 3, 0, 3, 1, 2, 1, 1, 2, 0]

theorem recover_059 : pairSubgroup 59 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 59 [0, 2, 2, 2, 1, 2, 0, 3, 0, 0, 0, 0, 2, 2, 2, 2, 1, 3, 0, 3] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 59 [0, 2, 2, 2, 1, 2, 0, 3, 0, 0, 0, 0, 2, 2, 2, 2, 1, 3, 0, 3]
  · have h : pairWord 59 [0, 2, 1, 2, 1, 1, 3, 3, 0, 3, 0, 0, 2, 2, 1, 3, 0, 0, 0, 0, 3] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 59 [0, 2, 1, 2, 1, 1, 3, 3, 0, 3, 0, 0, 2, 2, 1, 3, 0, 0, 0, 0, 3]

theorem recover_060 : pairSubgroup 60 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 60 [3, 1, 2, 2, 1, 2, 1, 1, 1, 3, 0, 3, 1, 3, 0, 0, 0, 3, 0, 2, 1, 2, 0, 2] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 60 [3, 1, 2, 2, 1, 2, 1, 1, 1, 3, 0, 3, 1, 3, 0, 0, 0, 3, 0, 2, 1, 2, 0, 2]
  · have h : pairWord 60 [1, 2, 1, 3, 3, 1, 2, 1, 1, 3, 0, 3, 1, 2, 1, 2, 1, 2, 2] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 60 [1, 2, 1, 3, 3, 1, 2, 1, 1, 3, 0, 3, 1, 2, 1, 2, 1, 2, 2]

theorem recover_061 : pairSubgroup 61 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 61 [2, 0, 3, 3, 0, 3, 0, 0, 2, 0, 0, 3, 3, 3, 1, 2, 0, 3, 1, 1, 1, 2, 1, 1, 3, 0, 0, 0, 2, 0, 3] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 61 [2, 0, 3, 3, 0, 3, 0, 0, 2, 0, 0, 3, 3, 3, 1, 2, 0, 3, 1, 1, 1, 2, 1, 1, 3, 0, 0, 0, 2, 0, 3]
  · have h : pairWord 61 [1, 2, 1, 1, 3, 0, 2, 1, 3, 3, 3, 1, 1, 1, 3, 3, 1] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 61 [1, 2, 1, 1, 3, 0, 2, 1, 3, 3, 3, 1, 1, 1, 3, 3, 1]

end Sporadic.LeechRelated.HS.SmallIndex.GenerationCertificate
