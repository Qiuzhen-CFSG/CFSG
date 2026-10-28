module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers.SmallIndex.Generation.Support

/-!
# Conjugate-pair recovery words, part 12

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

theorem recover_112 : pairSubgroup 112 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 112 [1, 3, 0, 2, 2, 1, 2, 2, 2, 2, 1, 3, 1, 3, 1, 2, 1, 3, 1, 1, 3, 1, 3, 3, 1, 1, 2] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 112 [1, 3, 0, 2, 2, 1, 2, 2, 2, 2, 1, 3, 1, 3, 1, 2, 1, 3, 1, 1, 3, 1, 3, 3, 1, 1, 2]
  · have h : pairWord 112 [3, 3, 3, 3, 0, 3, 1, 3, 1, 1, 1, 3, 3, 1, 2, 0, 3, 1, 1, 3, 3, 1] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 112 [3, 3, 3, 3, 0, 3, 1, 3, 1, 1, 1, 3, 3, 1, 2, 0, 3, 1, 1, 3, 3, 1]

theorem recover_113 : pairSubgroup 113 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 113 [1, 3, 1, 3, 0, 0, 0, 0, 0, 3, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 3] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 113 [1, 3, 1, 3, 0, 0, 0, 0, 0, 3, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 3]
  · have h : pairWord 113 [3, 1, 3, 0, 2, 1, 1, 3, 1, 2, 1, 3] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 113 [3, 1, 3, 0, 2, 1, 1, 3, 1, 2, 1, 3]

theorem recover_114 : pairSubgroup 114 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 114 [1, 3, 0, 0, 2, 2, 1, 2, 1, 3, 1, 3, 3, 1, 1, 3, 0, 3, 0, 0, 2, 2, 2] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 114 [1, 3, 0, 0, 2, 2, 1, 2, 1, 3, 1, 3, 3, 1, 1, 3, 0, 3, 0, 0, 2, 2, 2]
  · have h : pairWord 114 [2, 2, 1, 3, 1, 2, 1, 3, 3, 1, 1, 1, 2, 2, 0, 2, 0] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 114 [2, 2, 1, 3, 1, 2, 1, 3, 3, 1, 1, 1, 2, 2, 0, 2, 0]

theorem recover_115 : pairSubgroup 115 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 115 [0, 2, 1, 3, 1, 1, 2, 0, 2, 1, 2, 1, 2, 2, 1, 3, 0, 0, 2, 0, 0] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 115 [0, 2, 1, 3, 1, 1, 2, 0, 2, 1, 2, 1, 2, 2, 1, 3, 0, 0, 2, 0, 0]
  · have h : pairWord 115 [0, 2, 0, 2, 2, 0, 3, 0, 0, 3, 1, 2, 0, 3, 3, 3, 1] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 115 [0, 2, 0, 2, 2, 0, 3, 0, 0, 3, 1, 2, 0, 3, 3, 3, 1]

theorem recover_116 : pairSubgroup 116 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 116 [0, 3, 3, 3, 0, 0, 0, 2, 1, 1, 2, 1, 3, 0, 2, 1, 3, 0] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 116 [0, 3, 3, 3, 0, 0, 0, 2, 1, 1, 2, 1, 3, 0, 2, 1, 3, 0]
  · have h : pairWord 116 [1, 2, 1, 1, 1, 3, 1, 1, 2, 0, 3, 3, 1, 1, 3, 3, 3, 0, 0, 2, 0] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 116 [1, 2, 1, 1, 1, 3, 1, 1, 2, 0, 3, 3, 1, 1, 3, 3, 3, 0, 0, 2, 0]

theorem recover_117 : pairSubgroup 117 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 117 [2, 1, 3, 3, 3, 1, 1, 2, 2, 0, 3, 1, 2, 0, 3, 1, 3, 3, 1, 2, 2, 2, 1, 3, 1, 1, 2, 2, 2, 2] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 117 [2, 1, 3, 3, 3, 1, 1, 2, 2, 0, 3, 1, 2, 0, 3, 1, 3, 3, 1, 2, 2, 2, 1, 3, 1, 1, 2, 2, 2, 2]
  · have h : pairWord 117 [1, 1, 1, 3, 1, 3, 3, 1, 3, 0, 3, 1, 2, 1, 2, 0, 2, 1, 1, 2, 1, 1, 1] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 117 [1, 1, 1, 3, 1, 3, 3, 1, 3, 0, 3, 1, 2, 1, 2, 0, 2, 1, 1, 2, 1, 1, 1]

theorem recover_118 : pairSubgroup 118 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 118 [3, 1, 3, 1, 1, 2, 2, 0, 3, 1, 1, 1, 1, 3, 1, 2, 2, 2, 0, 0, 0, 0, 0, 0, 3, 1, 1, 1, 3, 1] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 118 [3, 1, 3, 1, 1, 2, 2, 0, 3, 1, 1, 1, 1, 3, 1, 2, 2, 2, 0, 0, 0, 0, 0, 0, 3, 1, 1, 1, 3, 1]
  · have h : pairWord 118 [1, 3, 1, 1, 3, 1, 2, 2, 0, 0, 0, 3, 0, 2, 1, 1, 2, 2, 1, 1] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 118 [1, 3, 1, 1, 3, 1, 2, 2, 0, 0, 0, 3, 0, 2, 1, 1, 2, 2, 1, 1]

theorem recover_119 : pairSubgroup 119 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 119 [0, 3, 0, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 0, 3, 1, 3, 3, 1, 2, 2, 2, 0, 3, 0, 2, 2] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 119 [0, 3, 0, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 0, 3, 1, 3, 3, 1, 2, 2, 2, 0, 3, 0, 2, 2]
  · have h : pairWord 119 [1, 2, 0, 2, 1, 1, 3, 1, 3, 3, 0, 2, 1] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 119 [1, 2, 0, 2, 1, 1, 3, 1, 3, 3, 0, 2, 1]

theorem recover_120 : pairSubgroup 120 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 120 [1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 3, 0, 2, 0, 0, 2, 2, 0] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 120 [1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 3, 0, 2, 0, 0, 2, 2, 0]
  · have h : pairWord 120 [1, 2, 2, 1, 1, 1, 3, 0, 2, 1, 3, 1, 3, 3, 0, 2, 2, 0, 2, 2, 1, 3, 3, 0, 3, 3] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 120 [1, 2, 2, 1, 1, 1, 3, 0, 2, 1, 3, 1, 3, 3, 0, 2, 2, 0, 2, 2, 1, 3, 3, 0, 3, 3]

theorem recover_121 : pairSubgroup 121 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 121 [2, 1, 3, 1, 3, 0, 2, 1, 2, 0, 2, 2, 1, 1, 1] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 121 [2, 1, 3, 1, 3, 0, 2, 1, 2, 0, 2, 2, 1, 1, 1]
  · have h : pairWord 121 [2, 2, 2, 2, 2, 2, 1, 2, 1, 1, 2, 1, 3, 0, 2, 2, 2, 0] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 121 [2, 2, 2, 2, 2, 2, 1, 2, 1, 1, 2, 1, 3, 0, 2, 2, 2, 0]

end Sporadic.LeechRelated.HS.SmallIndex.GenerationCertificate
