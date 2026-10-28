module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers.SmallIndex.Generation.Support

/-!
# Conjugate-pair recovery words, part 13

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

theorem recover_122 : pairSubgroup 122 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 122 [1, 3, 1, 2, 2, 0, 0, 2, 2, 1, 3, 1, 1, 2, 2, 1, 2, 1, 3, 3, 3, 0, 0, 2, 2] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 122 [1, 3, 1, 2, 2, 0, 0, 2, 2, 1, 3, 1, 1, 2, 2, 1, 2, 1, 3, 3, 3, 0, 0, 2, 2]
  · have h : pairWord 122 [2, 1, 3, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 0, 0, 0, 2, 1, 1, 1, 1, 2] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 122 [2, 1, 3, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 0, 0, 0, 2, 1, 1, 1, 1, 2]

theorem recover_123 : pairSubgroup 123 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 123 [3, 1, 2, 2, 0, 2, 0, 3, 0, 0, 0, 2, 0, 2, 1, 3, 3, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 3] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 123 [3, 1, 2, 2, 0, 2, 0, 3, 0, 0, 0, 2, 0, 2, 1, 3, 3, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 3]
  · have h : pairWord 123 [2, 0, 2, 0, 3, 0, 0, 3, 1, 1, 1, 1, 2, 0, 3, 0, 0, 0, 0, 2, 2] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 123 [2, 0, 2, 0, 3, 0, 0, 3, 1, 1, 1, 1, 2, 0, 3, 0, 0, 0, 0, 2, 2]

theorem recover_124 : pairSubgroup 124 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 124 [0, 3, 0, 2, 1, 1, 3, 1, 2, 0, 2, 0, 3, 1, 1, 1, 1, 2, 2, 0, 3, 3, 1, 1, 1, 1, 1, 1, 1] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 124 [0, 3, 0, 2, 1, 1, 3, 1, 2, 0, 2, 0, 3, 1, 1, 1, 1, 2, 2, 0, 3, 3, 1, 1, 1, 1, 1, 1, 1]
  · have h : pairWord 124 [3, 0, 2, 1, 1, 3, 1, 3, 3, 1, 2, 0, 3, 0, 0, 2, 0, 3, 3, 1, 1, 1] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 124 [3, 0, 2, 1, 1, 3, 1, 3, 3, 1, 2, 0, 3, 0, 0, 2, 0, 3, 3, 1, 1, 1]

theorem recover_125 : pairSubgroup 125 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 125 [2, 0, 0, 2, 1, 3, 1] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 125 [2, 0, 0, 2, 1, 3, 1]
  · have h : pairWord 125 [0, 2, 0, 3, 3, 0, 2, 0, 2, 2, 2, 1, 1, 1, 2, 0, 3, 1, 3, 0, 0, 3, 0, 3, 0, 0, 0, 0, 3, 1, 2] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 125 [0, 2, 0, 3, 3, 0, 2, 0, 2, 2, 2, 1, 1, 1, 2, 0, 3, 1, 3, 0, 0, 3, 0, 3, 0, 0, 0, 0, 3, 1, 2]

theorem recover_126 : pairSubgroup 126 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 126 [3, 3, 3, 0, 3, 0, 3, 3, 0, 0, 3, 0, 0, 0, 2, 2, 2] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 126 [3, 3, 3, 0, 3, 0, 3, 3, 0, 0, 3, 0, 0, 0, 2, 2, 2]
  · have h : pairWord 126 [0, 2, 0, 0, 3, 1, 1, 3, 1, 1, 3, 0, 2, 1, 3, 0, 3, 3, 1, 2, 1, 2, 1, 2, 2, 2] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 126 [0, 2, 0, 0, 3, 1, 1, 3, 1, 1, 3, 0, 2, 1, 3, 0, 3, 3, 1, 2, 1, 2, 1, 2, 2, 2]

theorem recover_127 : pairSubgroup 127 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 127 [1, 3, 1, 2, 0, 3, 1, 3, 3, 3, 3, 3, 3, 1, 2, 1, 1, 3, 1, 1, 1, 3] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 127 [1, 3, 1, 2, 0, 3, 1, 3, 3, 3, 3, 3, 3, 1, 2, 1, 1, 3, 1, 1, 1, 3]
  · have h : pairWord 127 [1, 2, 1, 1, 1, 2, 1, 1, 3, 0, 2, 1, 3, 0, 0, 3, 0] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 127 [1, 2, 1, 1, 1, 2, 1, 1, 3, 0, 2, 1, 3, 0, 0, 3, 0]

theorem recover_128 : pairSubgroup 128 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 128 [1, 1, 2, 2, 2, 1, 3, 3, 3, 3, 0, 2, 1, 1, 3, 0, 0, 0, 3, 1, 1, 2, 2, 1, 3, 3, 0, 2] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 128 [1, 1, 2, 2, 2, 1, 3, 3, 3, 3, 0, 2, 1, 1, 3, 0, 0, 0, 3, 1, 1, 2, 2, 1, 3, 3, 0, 2]
  · have h : pairWord 128 [2, 0, 2, 1, 3, 1, 3, 1, 1, 3, 3, 3, 0, 3, 3, 0, 2] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 128 [2, 0, 2, 1, 3, 1, 3, 1, 1, 3, 3, 3, 0, 3, 3, 0, 2]

theorem recover_129 : pairSubgroup 129 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 129 [1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 2, 2, 0, 0, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 129 [1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 2, 2, 0, 0, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1]
  · have h : pairWord 129 [1, 1, 3, 0, 3, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 0, 2, 2, 1, 1, 3, 0] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 129 [1, 1, 3, 0, 3, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 0, 2, 2, 1, 1, 3, 0]

theorem recover_130 : pairSubgroup 130 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 130 [2, 2, 0, 2, 1, 2, 2, 0, 0, 3, 1, 2, 1, 2, 0, 3, 0, 0, 0, 0, 2, 0, 3, 0, 0, 3, 0, 2, 2] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 130 [2, 2, 0, 2, 1, 2, 2, 0, 0, 3, 1, 2, 1, 2, 0, 3, 0, 0, 0, 0, 2, 0, 3, 0, 0, 3, 0, 2, 2]
  · have h : pairWord 130 [1, 2, 0, 0, 2, 1, 3, 1, 1, 1, 2, 0, 0, 3, 0, 0, 0, 0, 2, 1, 2] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 130 [1, 2, 0, 0, 2, 1, 3, 1, 1, 1, 2, 0, 0, 3, 0, 0, 0, 0, 2, 1, 2]

theorem recover_131 : pairSubgroup 131 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 131 [3, 3, 0, 0, 2, 0, 3, 1, 3, 0, 0, 0, 0, 0, 3, 1, 2, 0, 2, 0, 2, 2, 0, 0, 2] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 131 [3, 3, 0, 0, 2, 0, 3, 1, 3, 0, 0, 0, 0, 0, 3, 1, 2, 0, 2, 0, 2, 2, 0, 0, 2]
  · have h : pairWord 131 [3, 3, 0, 0, 2, 0, 2, 2, 2, 0, 2, 1, 1, 2, 1, 2, 0, 0, 2, 1, 3, 0, 0, 3, 1] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 131 [3, 3, 0, 0, 2, 0, 2, 2, 2, 0, 2, 1, 1, 2, 1, 2, 0, 0, 2, 1, 3, 0, 0, 3, 1]

end Sporadic.LeechRelated.HS.SmallIndex.GenerationCertificate
