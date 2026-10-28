module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers.SmallIndex.Generation.Support

/-!
# Conjugate-pair recovery words, part 15

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

theorem recover_142 : pairSubgroup 142 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 142 [3, 3, 1, 3, 3, 0, 2, 2, 0] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 142 [3, 3, 1, 3, 3, 0, 2, 2, 0]
  · have h : pairWord 142 [1, 1, 3, 3, 0, 3, 1, 3, 0, 2, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 0, 0, 3, 3] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 142 [1, 1, 3, 3, 0, 3, 1, 3, 0, 2, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 0, 0, 3, 3]

theorem recover_143 : pairSubgroup 143 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 143 [1, 3, 0, 2, 1, 1, 2, 2, 2, 2, 2, 0, 0, 0, 0, 2] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 143 [1, 3, 0, 2, 1, 1, 2, 2, 2, 2, 2, 0, 0, 0, 0, 2]
  · have h : pairWord 143 [3, 3, 1, 1, 2, 0, 3, 3, 1, 3, 1, 2, 1, 1, 3, 1, 1, 2, 2, 0] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 143 [3, 3, 1, 1, 2, 0, 3, 3, 1, 3, 1, 2, 1, 1, 3, 1, 1, 2, 2, 0]

theorem recover_144 : pairSubgroup 144 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 144 [0, 2, 1, 1, 3, 3, 3, 3, 0, 3, 0, 2, 0, 0, 2, 0, 2, 1] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 144 [0, 2, 1, 1, 3, 3, 3, 3, 0, 3, 0, 2, 0, 0, 2, 0, 2, 1]
  · have h : pairWord 144 [1, 3, 0, 2, 0, 2, 1, 1, 3, 3, 3, 1, 2, 0, 0, 2, 0, 0] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 144 [1, 3, 0, 2, 0, 2, 1, 1, 3, 3, 3, 1, 2, 0, 0, 2, 0, 0]

theorem recover_145 : pairSubgroup 145 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 145 [1, 3, 3, 3, 3, 3, 0, 2, 1, 2, 1, 3, 1, 1, 3, 3, 0, 3, 3, 0, 3, 0] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 145 [1, 3, 3, 3, 3, 3, 0, 2, 1, 2, 1, 3, 1, 1, 3, 3, 0, 3, 3, 0, 3, 0]
  · have h : pairWord 145 [1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 2, 0, 3, 0, 0, 2, 0, 2, 1, 2, 1, 1] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 145 [1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 2, 0, 3, 0, 0, 2, 0, 2, 1, 2, 1, 1]

theorem recover_146 : pairSubgroup 146 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 146 [3, 0, 0, 3, 3, 1, 2, 1, 1, 3, 0, 0, 2, 1, 3, 3, 1, 2, 1] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 146 [3, 0, 0, 3, 3, 1, 2, 1, 1, 3, 0, 0, 2, 1, 3, 3, 1, 2, 1]
  · have h : pairWord 146 [0, 3, 1, 1, 1, 3, 1, 2, 2, 2, 0, 3, 0, 0, 0, 3, 1, 2, 0, 3, 0, 0] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 146 [0, 3, 1, 1, 1, 3, 1, 2, 2, 2, 0, 3, 0, 0, 0, 3, 1, 2, 0, 3, 0, 0]

theorem recover_147 : pairSubgroup 147 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 147 [0, 3, 3, 0, 2, 0, 0, 0, 2, 2, 0, 3, 0, 3, 3, 3, 1, 2, 0, 3, 1, 3, 1, 2] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 147 [0, 3, 3, 0, 2, 0, 0, 0, 2, 2, 0, 3, 0, 3, 3, 3, 1, 2, 0, 3, 1, 3, 1, 2]
  · have h : pairWord 147 [3, 3, 0, 3, 1, 1, 1, 2, 0, 2, 1, 3, 3, 0] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 147 [3, 3, 0, 3, 1, 1, 1, 2, 0, 2, 1, 3, 3, 0]

theorem recover_148 : pairSubgroup 148 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 148 [1, 2, 2, 2, 2, 1, 2, 2, 2, 2] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 148 [1, 2, 2, 2, 2, 1, 2, 2, 2, 2]
  · have h : pairWord 148 [0, 3, 1, 3, 1, 1, 3, 0, 2, 2, 1, 1, 3, 3, 3, 0, 3, 3, 1] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 148 [0, 3, 1, 3, 1, 1, 3, 0, 2, 2, 1, 1, 3, 3, 3, 0, 3, 3, 1]

theorem recover_149 : pairSubgroup 149 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 149 [1, 1, 1, 1, 3, 0, 0, 3, 0, 3, 3, 1, 3, 3, 1, 1, 1, 2, 1, 3, 1, 1, 1] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 149 [1, 1, 1, 1, 3, 0, 0, 3, 0, 3, 3, 1, 3, 3, 1, 1, 1, 2, 1, 3, 1, 1, 1]
  · have h : pairWord 149 [1, 2, 1, 3, 1, 1, 2, 0, 2, 2, 0, 3, 0, 0, 0, 0, 3, 0, 2] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 149 [1, 2, 1, 3, 1, 1, 2, 0, 2, 2, 0, 3, 0, 0, 0, 0, 3, 0, 2]

end Sporadic.LeechRelated.HS.SmallIndex.GenerationCertificate
