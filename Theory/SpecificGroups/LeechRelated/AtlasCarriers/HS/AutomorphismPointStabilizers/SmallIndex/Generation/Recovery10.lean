module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers.SmallIndex.Generation.Support

/-!
# Conjugate-pair recovery words, part 11

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

theorem recover_102 : pairSubgroup 102 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 102 [2, 1, 2, 1, 2, 1, 3, 0, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 102 [2, 1, 2, 1, 2, 1, 3, 0, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3]
  · have h : pairWord 102 [2, 1, 2, 1, 3, 3, 1, 2, 0, 0, 0, 0, 0, 0, 3, 1] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 102 [2, 1, 2, 1, 3, 3, 1, 2, 0, 0, 0, 0, 0, 0, 3, 1]

theorem recover_103 : pairSubgroup 103 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 103 [2, 1, 2, 2, 0, 3, 0, 3, 0, 3, 0, 0, 3, 1, 1, 2, 2, 1, 2, 1, 3, 1] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 103 [2, 1, 2, 2, 0, 3, 0, 3, 0, 3, 0, 0, 3, 1, 1, 2, 2, 1, 2, 1, 3, 1]
  · have h : pairWord 103 [0, 0, 0, 0, 2, 1, 1, 1, 1, 2, 2, 2, 0, 2, 1, 2, 0, 2, 2] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 103 [0, 0, 0, 0, 2, 1, 1, 1, 1, 2, 2, 2, 0, 2, 1, 2, 0, 2, 2]

theorem recover_104 : pairSubgroup 104 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 104 [2, 1, 2, 0, 3, 1, 1, 1, 2, 1, 2, 2, 0, 0, 3, 0, 3, 3, 3, 0, 3, 1, 1, 1, 1, 1] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 104 [2, 1, 2, 0, 3, 1, 1, 1, 2, 1, 2, 2, 0, 0, 3, 0, 3, 3, 3, 0, 3, 1, 1, 1, 1, 1]
  · have h : pairWord 104 [1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 0, 0, 0, 2, 2, 0, 0, 0, 2, 1, 3, 0, 3] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 104 [1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 0, 0, 0, 2, 2, 0, 0, 0, 2, 1, 3, 0, 3]

theorem recover_105 : pairSubgroup 105 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 105 [0, 0, 3, 3, 0, 2, 2, 2, 2, 2, 1, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3, 0, 0, 3, 1] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 105 [0, 0, 3, 3, 0, 2, 2, 2, 2, 2, 1, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3, 0, 0, 3, 1]
  · have h : pairWord 105 [3, 3, 3, 1, 2, 2, 1, 1, 2, 2, 0, 0, 2, 1, 1, 1, 2, 0, 0, 3, 1, 2, 1, 3, 0, 3, 1, 1] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 105 [3, 3, 3, 1, 2, 2, 1, 1, 2, 2, 0, 0, 2, 1, 1, 1, 2, 0, 0, 3, 1, 2, 1, 3, 0, 3, 1, 1]

theorem recover_106 : pairSubgroup 106 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 106 [1, 2, 1, 3, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 3, 0, 3, 0, 3, 3, 3, 0, 2, 2, 1, 3, 3] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 106 [1, 2, 1, 3, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 3, 0, 3, 0, 3, 3, 3, 0, 2, 2, 1, 3, 3]
  · have h : pairWord 106 [3, 0, 3, 0, 2, 2, 2, 1, 3, 0, 2, 0, 0, 0, 2, 0, 3, 0] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 106 [3, 0, 3, 0, 2, 2, 2, 1, 3, 0, 2, 0, 0, 0, 2, 0, 3, 0]

theorem recover_107 : pairSubgroup 107 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 107 [0, 3, 1, 3, 3, 3, 0, 0, 3, 3, 1, 3, 0, 3, 3, 1, 1, 1, 3, 0, 0, 3] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 107 [0, 3, 1, 3, 3, 3, 0, 0, 3, 3, 1, 3, 0, 3, 3, 1, 1, 1, 3, 0, 0, 3]
  · have h : pairWord 107 [0, 2, 0, 0, 3, 0, 3, 0, 0, 0, 0, 3, 1, 1, 3] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 107 [0, 2, 0, 0, 3, 0, 3, 0, 0, 0, 0, 3, 1, 1, 3]

theorem recover_108 : pairSubgroup 108 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 108 [3, 0, 2, 0, 3, 0, 0, 2, 1, 3, 3, 3, 1, 3, 1, 2, 1, 3, 3, 0, 2, 0, 3, 1] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 108 [3, 0, 2, 0, 3, 0, 0, 2, 1, 3, 3, 3, 1, 3, 1, 2, 1, 3, 3, 0, 2, 0, 3, 1]
  · have h : pairWord 108 [2, 2, 0, 0, 2, 1, 1, 3, 3, 0, 0, 0, 0, 3, 3, 3] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 108 [2, 2, 0, 0, 2, 1, 1, 3, 3, 0, 0, 0, 0, 3, 3, 3]

theorem recover_109 : pairSubgroup 109 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 109 [2, 1, 3, 1, 1, 2, 2, 2, 0, 0, 3, 0, 3, 0, 2, 0, 2, 2, 0, 2, 0, 3, 3, 3, 3, 0, 3, 1, 1] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 109 [2, 1, 3, 1, 1, 2, 2, 2, 0, 0, 3, 0, 3, 0, 2, 0, 2, 2, 0, 2, 0, 3, 3, 3, 3, 0, 3, 1, 1]
  · have h : pairWord 109 [2, 0, 3, 1, 1, 1, 2, 0, 0, 2, 1, 1, 3, 3, 3, 3, 0, 0, 2, 0, 3] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 109 [2, 0, 3, 1, 1, 1, 2, 0, 0, 2, 1, 1, 3, 3, 3, 3, 0, 0, 2, 0, 3]

theorem recover_110 : pairSubgroup 110 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 110 [0, 2, 0, 0, 0, 3, 0, 3, 0, 0, 0, 3] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 110 [0, 2, 0, 0, 0, 3, 0, 3, 0, 0, 0, 3]
  · have h : pairWord 110 [3, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 0, 2, 2, 0, 2, 1, 1, 3, 0, 3, 1, 2, 0, 3] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 110 [3, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 0, 2, 2, 0, 2, 1, 1, 3, 0, 3, 1, 2, 0, 3]

theorem recover_111 : pairSubgroup 111 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 111 [3, 1, 2, 1, 2, 0, 3, 3, 1, 2, 2, 1, 3, 3, 1, 1, 1, 1, 1, 1, 3, 0, 2, 2, 2, 2, 0, 0] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 111 [3, 1, 2, 1, 2, 0, 3, 3, 1, 2, 2, 1, 3, 3, 1, 1, 1, 1, 1, 1, 3, 0, 2, 2, 2, 2, 0, 0]
  · have h : pairWord 111 [0, 0, 0, 2, 0, 2, 0, 2, 2, 2, 0, 0, 0, 3, 1, 2, 0, 2] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 111 [0, 0, 0, 2, 0, 2, 0, 2, 2, 2, 0, 0, 0, 3, 1, 2, 0, 2]

end Sporadic.LeechRelated.HS.SmallIndex.GenerationCertificate
