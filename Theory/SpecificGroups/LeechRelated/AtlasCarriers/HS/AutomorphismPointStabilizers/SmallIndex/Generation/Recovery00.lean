module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers.SmallIndex.Generation.Support

/-!
# Conjugate-pair recovery words, part 1

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

theorem recover_002 : pairSubgroup 2 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 2 [1, 2, 2, 0, 2, 1, 3, 1, 2, 1, 1, 2, 0, 0, 3, 1, 2, 1, 3, 1, 2, 2, 2, 2] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 2 [1, 2, 2, 0, 2, 1, 3, 1, 2, 1, 1, 2, 0, 0, 3, 1, 2, 1, 3, 1, 2, 2, 2, 2]
  · have h : pairWord 2 [0, 0, 2, 2, 2, 0, 3, 0, 2, 2, 0, 3, 0, 0, 3, 1, 1, 2] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 2 [0, 0, 2, 2, 2, 0, 3, 0, 2, 2, 0, 3, 0, 0, 3, 1, 1, 2]

theorem recover_003 : pairSubgroup 3 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 3 [3, 1, 3, 3, 0, 2, 0, 0, 0, 3, 0, 0, 2, 1, 1, 2, 2, 2, 0, 3, 1, 2] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 3 [3, 1, 3, 3, 0, 2, 0, 0, 0, 3, 0, 0, 2, 1, 1, 2, 2, 2, 0, 3, 1, 2]
  · have h : pairWord 3 [1, 2, 2, 2, 1, 2, 0, 2, 2, 0, 0, 2, 0, 0, 2, 2, 1, 1, 2, 1, 2, 0, 3, 3, 3, 0, 0, 3] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 3 [1, 2, 2, 2, 1, 2, 0, 2, 2, 0, 0, 2, 0, 0, 2, 2, 1, 1, 2, 1, 2, 0, 3, 3, 3, 0, 0, 3]

theorem recover_004 : pairSubgroup 4 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 4 [0, 2, 0, 0, 0, 3, 1, 1, 2, 0, 0, 0, 0, 0, 2, 2, 2, 1, 1] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 4 [0, 2, 0, 0, 0, 3, 1, 1, 2, 0, 0, 0, 0, 0, 2, 2, 2, 1, 1]
  · have h : pairWord 4 [1, 1, 1, 2, 0, 0, 3, 0, 0, 2, 1, 1, 3, 3, 3, 0, 0, 2, 1, 1, 1, 3, 1] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 4 [1, 1, 1, 2, 0, 0, 3, 0, 0, 2, 1, 1, 3, 3, 3, 0, 0, 2, 1, 1, 1, 3, 1]

theorem recover_005 : pairSubgroup 5 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 5 [2, 2, 2, 1, 1, 1, 2, 0, 0, 0, 2, 2, 0, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 5 [2, 2, 2, 1, 1, 1, 2, 0, 0, 0, 2, 2, 0, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2]
  · have h : pairWord 5 [0, 0, 2, 0, 3, 1, 2, 1, 1, 1, 3, 0, 3, 0, 3, 1, 1, 2, 2, 1, 1, 1] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 5 [0, 0, 2, 0, 3, 1, 2, 1, 1, 1, 3, 0, 3, 0, 3, 1, 1, 2, 2, 1, 1, 1]

theorem recover_006 : pairSubgroup 6 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 6 [2, 0, 0, 3, 1, 3, 3, 0, 2, 2, 0, 0, 2, 0, 3, 1] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 6 [2, 0, 0, 3, 1, 3, 3, 0, 2, 2, 0, 0, 2, 0, 3, 1]
  · have h : pairWord 6 [1, 1, 1, 2, 2, 0, 0, 2, 2, 1, 1, 2, 1, 2, 1, 2, 0, 2, 0, 3, 0, 2, 2, 2, 1] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 6 [1, 1, 1, 2, 2, 0, 0, 2, 2, 1, 1, 2, 1, 2, 1, 2, 0, 2, 0, 3, 0, 2, 2, 2, 1]

theorem recover_007 : pairSubgroup 7 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 7 [1, 2, 2, 1, 3, 1, 1, 2, 2, 2, 1, 1, 2, 0, 3, 3, 1, 2, 2, 2, 1, 3, 1, 2, 1, 1, 3] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 7 [1, 2, 2, 1, 3, 1, 1, 2, 2, 2, 1, 1, 2, 0, 3, 3, 1, 2, 2, 2, 1, 3, 1, 2, 1, 1, 3]
  · have h : pairWord 7 [2, 0, 2, 1, 3, 3, 3, 0, 0, 0, 2, 0, 0, 0, 2, 0, 3, 0, 0, 3, 0, 0, 0] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 7 [2, 0, 2, 1, 3, 3, 3, 0, 0, 0, 2, 0, 0, 0, 2, 0, 3, 0, 0, 3, 0, 0, 0]

theorem recover_008 : pairSubgroup 8 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 8 [0, 3, 0, 3, 0, 0, 3, 3, 1, 3, 3, 0, 3, 0, 0, 2, 1, 3, 1, 3, 0, 3, 1, 1] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 8 [0, 3, 0, 3, 0, 0, 3, 3, 1, 3, 3, 0, 3, 0, 0, 2, 1, 3, 1, 3, 0, 3, 1, 1]
  · have h : pairWord 8 [0, 0, 2, 0, 3, 1, 3, 1, 1, 2, 2, 0, 0, 0, 0, 3, 3, 1, 3, 0, 3, 0, 0, 3] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 8 [0, 0, 2, 0, 3, 1, 3, 1, 1, 2, 2, 0, 0, 0, 0, 3, 3, 1, 3, 0, 3, 0, 0, 3]

theorem recover_009 : pairSubgroup 9 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 9 [2, 2, 0, 3, 1, 2, 0, 3, 0, 0, 3, 3, 3, 0, 2, 1, 3, 1, 1, 1, 1, 1] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 9 [2, 2, 0, 3, 1, 2, 0, 3, 0, 0, 3, 3, 3, 0, 2, 1, 3, 1, 1, 1, 1, 1]
  · have h : pairWord 9 [0, 2, 1, 1, 2, 0, 3, 1, 3, 0, 0, 2, 1, 3, 1, 3, 3, 3, 3, 1, 2, 1, 1, 2, 1, 2, 2, 0] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 9 [0, 2, 1, 1, 2, 0, 3, 1, 3, 0, 0, 2, 1, 3, 1, 3, 3, 3, 3, 1, 2, 1, 1, 2, 1, 2, 2, 0]

theorem recover_010 : pairSubgroup 10 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 10 [2, 2, 2, 0, 0, 3, 1, 1, 2, 0, 0, 3, 0, 0, 3, 1, 3, 0, 2, 0, 2, 0, 3, 0, 0, 2, 0] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 10 [2, 2, 2, 0, 0, 3, 1, 1, 2, 0, 0, 3, 0, 0, 3, 1, 3, 0, 2, 0, 2, 0, 3, 0, 0, 2, 0]
  · have h : pairWord 10 [3, 3, 0, 0, 0, 2, 1, 3, 0, 0, 0, 2, 1, 1, 3, 3, 3] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 10 [3, 3, 0, 0, 0, 2, 1, 3, 0, 0, 0, 2, 1, 1, 3, 3, 3]

theorem recover_011 : pairSubgroup 11 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 11 [1, 2, 0, 2, 2, 1, 1, 3, 3, 3, 3, 3, 3, 3, 0] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 11 [1, 2, 0, 2, 2, 1, 1, 3, 3, 3, 3, 3, 3, 3, 0]
  · have h : pairWord 11 [3, 1, 1, 1, 2, 0, 2, 0, 2, 0, 0, 3, 3, 1, 1, 1, 1, 3, 1] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 11 [3, 1, 1, 1, 2, 0, 2, 0, 2, 0, 0, 3, 3, 1, 1, 1, 1, 3, 1]

end Sporadic.LeechRelated.HS.SmallIndex.GenerationCertificate
