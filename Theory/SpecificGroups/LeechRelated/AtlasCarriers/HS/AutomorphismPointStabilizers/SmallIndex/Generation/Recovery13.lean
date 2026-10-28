module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers.SmallIndex.Generation.Support

/-!
# Conjugate-pair recovery words, part 14

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

theorem recover_132 : pairSubgroup 132 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 132 [1, 3, 1] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 132 [1, 3, 1]
  · have h : pairWord 132 [1, 3, 3, 0, 0, 3, 3, 1, 3, 3, 0, 3, 3, 0, 2, 1, 2, 1, 2, 1] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 132 [1, 3, 3, 0, 0, 3, 3, 1, 3, 3, 0, 3, 3, 0, 2, 1, 2, 1, 2, 1]

theorem recover_133 : pairSubgroup 133 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 133 [3, 0, 0, 2, 1, 2, 1, 2, 0, 0, 3, 0, 3, 0, 2, 2, 0, 0, 0, 0, 3, 3, 1, 3, 3, 3] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 133 [3, 0, 0, 2, 1, 2, 1, 2, 0, 0, 3, 0, 3, 0, 2, 2, 0, 0, 0, 0, 3, 3, 1, 3, 3, 3]
  · have h : pairWord 133 [0, 3, 0, 2, 2, 1, 1, 2, 0, 2, 1, 1, 1, 3, 0, 3, 1, 3, 3, 0] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 133 [0, 3, 0, 2, 2, 1, 1, 2, 0, 2, 1, 1, 1, 3, 0, 3, 1, 3, 3, 0]

theorem recover_134 : pairSubgroup 134 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 134 [2, 1, 2, 1, 1, 1, 2, 0, 2, 1, 1, 2, 1, 3, 0, 2, 0, 3, 1, 3, 0, 3, 0, 3, 1] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 134 [2, 1, 2, 1, 1, 1, 2, 0, 2, 1, 1, 2, 1, 3, 0, 2, 0, 3, 1, 3, 0, 3, 0, 3, 1]
  · have h : pairWord 134 [2, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 134 [2, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1]

theorem recover_135 : pairSubgroup 135 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 135 [3, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 2, 0, 3, 1, 2, 0, 3, 1, 2, 2, 1, 3, 1, 1] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 135 [3, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 2, 0, 3, 1, 2, 0, 3, 1, 2, 2, 1, 3, 1, 1]
  · have h : pairWord 135 [2, 2, 2, 1, 1, 3, 0, 2, 1, 3, 0, 2, 0, 0, 3, 0, 0, 0, 3, 0, 3, 0] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 135 [2, 2, 2, 1, 1, 3, 0, 2, 1, 3, 0, 2, 0, 0, 3, 0, 0, 0, 3, 0, 3, 0]

theorem recover_136 : pairSubgroup 136 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 136 [3, 3, 1, 2, 1, 3, 0, 0, 0, 3, 3, 3, 1, 2, 2, 0, 2, 2, 0, 0, 3, 0, 3, 1, 2, 2] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 136 [3, 3, 1, 2, 1, 3, 0, 0, 0, 3, 3, 3, 1, 2, 2, 0, 2, 2, 0, 0, 3, 0, 3, 1, 2, 2]
  · have h : pairWord 136 [0, 3, 1, 2, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 2, 0, 0, 3] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 136 [0, 3, 1, 2, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 2, 0, 0, 3]

theorem recover_137 : pairSubgroup 137 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 137 [3, 3, 0, 2, 0, 2, 2, 2, 1, 2, 2, 1, 3, 3, 0, 2, 2, 1, 2, 0, 2, 0, 3, 0, 3, 3, 3, 0, 2, 0] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 137 [3, 3, 0, 2, 0, 2, 2, 2, 1, 2, 2, 1, 3, 3, 0, 2, 2, 1, 2, 0, 2, 0, 3, 0, 3, 3, 3, 0, 2, 0]
  · have h : pairWord 137 [3, 3, 3, 1, 3, 1, 2, 2, 0, 2, 2, 2, 1, 1, 2, 2, 1, 1, 3, 0, 2, 2, 2] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 137 [3, 3, 3, 1, 3, 1, 2, 2, 0, 2, 2, 2, 1, 1, 2, 2, 1, 1, 3, 0, 2, 2, 2]

theorem recover_138 : pairSubgroup 138 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 138 [0, 2, 2, 2, 0, 3, 1, 2, 0, 0, 3, 1, 3, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 138 [0, 2, 2, 2, 0, 3, 1, 2, 0, 0, 3, 1, 3, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3]
  · have h : pairWord 138 [2, 0, 2, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 0, 0, 2, 0, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 138 [2, 0, 2, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 0, 0, 2, 0, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2]

theorem recover_139 : pairSubgroup 139 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 139 [3, 1, 3, 0, 0, 2, 2, 0, 3, 1, 1] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 139 [3, 1, 3, 0, 0, 2, 2, 0, 3, 1, 1]
  · have h : pairWord 139 [3, 1, 3, 3, 0, 2, 0, 0, 3, 3, 0, 0, 0, 2, 1, 2, 2, 0, 3, 3, 0, 3, 3, 1] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 139 [3, 1, 3, 3, 0, 2, 0, 0, 3, 3, 0, 0, 0, 2, 1, 2, 2, 0, 3, 3, 0, 3, 3, 1]

theorem recover_140 : pairSubgroup 140 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 140 [2, 0, 3, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 140 [2, 0, 3, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1]
  · have h : pairWord 140 [0, 0, 0, 2, 0, 2, 1, 3, 0, 0, 3, 3, 3, 0, 0, 0, 3, 1, 3, 3, 0, 2, 1] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 140 [0, 0, 0, 2, 0, 2, 1, 3, 0, 0, 3, 3, 3, 0, 0, 0, 3, 1, 3, 3, 0, 2, 1]

theorem recover_141 : pairSubgroup 141 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 141 [3, 1, 2, 2, 1, 3, 0, 3, 0, 2, 2, 2, 0, 0, 0, 2, 0, 0] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 141 [3, 1, 2, 2, 1, 3, 0, 3, 0, 2, 2, 2, 0, 0, 0, 2, 0, 0]
  · have h : pairWord 141 [1, 2, 0, 3, 3, 0, 2, 0, 2, 2, 0, 3, 0, 2, 1, 3, 0, 0, 3, 3] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 141 [1, 2, 0, 3, 3, 0, 2, 0, 2, 2, 0, 3, 0, 2, 1, 3, 0, 0, 3, 3]

end Sporadic.LeechRelated.HS.SmallIndex.GenerationCertificate
