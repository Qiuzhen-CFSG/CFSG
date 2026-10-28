module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers.SmallIndex.Generation.Support

/-!
# Conjugate-pair recovery words, part 8

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

theorem recover_072 : pairSubgroup 72 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 72 [2, 1, 3, 0, 3, 1, 2, 1, 2, 0, 2, 2, 1, 2, 2, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 72 [2, 1, 3, 0, 3, 1, 2, 1, 2, 0, 2, 2, 1, 2, 2, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1]
  · have h : pairWord 72 [2, 0, 2, 2, 1, 2, 2, 2, 2, 1, 1, 3, 0, 0, 0, 0, 2, 1, 1, 1, 2, 0] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 72 [2, 0, 2, 2, 1, 2, 2, 2, 2, 1, 1, 3, 0, 0, 0, 0, 2, 1, 1, 1, 2, 0]

theorem recover_073 : pairSubgroup 73 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 73 [0, 2, 0, 0, 3, 3, 3, 1, 3, 0, 3, 3, 0, 2, 0, 2, 1, 2, 2, 1, 3, 1, 3, 0, 0, 0, 2, 0] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 73 [0, 2, 0, 0, 3, 3, 3, 1, 3, 0, 3, 3, 0, 2, 0, 2, 1, 2, 2, 1, 3, 1, 3, 0, 0, 0, 2, 0]
  · have h : pairWord 73 [0, 2, 1, 2, 0, 0, 2, 1, 1, 2, 1, 3, 0, 3, 1, 3, 1, 1, 2, 1, 2, 0, 0, 3, 3] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 73 [0, 2, 1, 2, 0, 0, 2, 1, 1, 2, 1, 3, 0, 3, 1, 3, 1, 1, 2, 1, 2, 0, 0, 3, 3]

theorem recover_074 : pairSubgroup 74 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 74 [1, 3, 3, 3, 1, 1, 2, 2, 2, 0, 3, 0, 2, 1, 1, 3, 3, 0] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 74 [1, 3, 3, 3, 1, 1, 2, 2, 2, 0, 3, 0, 2, 1, 1, 3, 3, 0]
  · have h : pairWord 74 [1, 3, 1, 2, 2, 1, 3, 1, 3, 1, 1, 3, 3, 1, 3, 1, 1] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 74 [1, 3, 1, 2, 2, 1, 3, 1, 3, 1, 1, 3, 3, 1, 3, 1, 1]

theorem recover_075 : pairSubgroup 75 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 75 [0, 3, 1, 2, 1, 1, 3, 0, 2, 2, 0, 3, 0, 2, 2, 1, 2, 2, 2, 0, 0, 0] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 75 [0, 3, 1, 2, 1, 1, 3, 0, 2, 2, 0, 3, 0, 2, 2, 1, 2, 2, 2, 0, 0, 0]
  · have h : pairWord 75 [1, 2, 2, 2, 0, 3, 3, 1, 1, 1, 3, 0, 3, 1, 1, 3, 1, 1, 2, 1, 2, 0] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 75 [1, 2, 2, 2, 0, 3, 3, 1, 1, 1, 3, 0, 3, 1, 1, 3, 1, 1, 2, 1, 2, 0]

theorem recover_076 : pairSubgroup 76 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 76 [3, 1, 1, 3, 3, 1, 1, 3, 0, 0, 2, 2, 1, 3, 3, 1, 3, 1, 2, 0, 0, 2, 1, 2, 0, 0] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 76 [3, 1, 1, 3, 3, 1, 1, 3, 0, 0, 2, 2, 1, 3, 3, 1, 3, 1, 2, 0, 0, 2, 1, 2, 0, 0]
  · have h : pairWord 76 [1, 2, 1, 3, 1, 1, 3, 1, 1, 1, 2, 0, 0, 0, 2, 2, 2] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 76 [1, 2, 1, 3, 1, 1, 3, 1, 1, 1, 2, 0, 0, 0, 2, 2, 2]

theorem recover_077 : pairSubgroup 77 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 77 [1, 3, 0, 0, 3, 3, 3, 3, 0, 0, 0, 2, 1, 2, 1, 2, 1, 1] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 77 [1, 3, 0, 0, 3, 3, 3, 3, 0, 0, 0, 2, 1, 2, 1, 2, 1, 1]
  · have h : pairWord 77 [1, 3, 1, 2, 1, 3, 1, 3, 3, 3, 0, 0, 0, 0, 0, 2, 1, 2, 0, 3, 1] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 77 [1, 3, 1, 2, 1, 3, 1, 3, 3, 3, 0, 0, 0, 0, 0, 2, 1, 2, 0, 3, 1]

theorem recover_078 : pairSubgroup 78 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 78 [3, 3, 0, 2, 2, 0, 3, 3, 1, 3, 1, 2, 2, 2, 0, 3, 0, 0, 2, 0, 2, 0, 0, 0, 3, 1, 1, 3, 3] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 78 [3, 3, 0, 2, 2, 0, 3, 3, 1, 3, 1, 2, 2, 2, 0, 3, 0, 0, 2, 0, 2, 0, 0, 0, 3, 1, 1, 3, 3]
  · have h : pairWord 78 [0, 2, 2, 2, 0, 3, 0, 3, 1, 1, 1, 3, 3, 3, 0, 0, 0, 0, 0, 2, 1] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 78 [0, 2, 2, 2, 0, 3, 0, 3, 1, 1, 1, 3, 3, 3, 0, 0, 0, 0, 0, 2, 1]

theorem recover_079 : pairSubgroup 79 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 79 [2, 0, 2, 0, 3, 1, 1, 2, 2, 0, 2, 2, 2, 1, 3, 3, 1, 2, 1, 3, 0, 0, 2, 2, 0] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 79 [2, 0, 2, 0, 3, 1, 1, 2, 2, 0, 2, 2, 2, 1, 3, 3, 1, 2, 1, 3, 0, 0, 2, 2, 0]
  · have h : pairWord 79 [3, 1, 3, 0, 0, 0, 2, 1, 2, 1, 2, 1, 3, 0, 3, 1, 2, 2] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 79 [3, 1, 3, 0, 0, 0, 2, 1, 2, 1, 2, 1, 3, 0, 3, 1, 2, 2]

theorem recover_080 : pairSubgroup 80 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 80 [1, 1, 3, 3, 0, 0, 3, 3, 0, 0, 3, 1, 2, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 1, 2, 1] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 80 [1, 1, 3, 3, 0, 0, 3, 3, 0, 0, 3, 1, 2, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 1, 2, 1]
  · have h : pairWord 80 [1, 1, 2, 2, 1, 1, 2, 2, 0, 0, 0, 2, 0, 3, 0, 0, 3, 0, 0, 2, 0, 0, 3, 1, 3, 3, 3, 3] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 80 [1, 1, 2, 2, 1, 1, 2, 2, 0, 0, 0, 2, 0, 3, 0, 0, 3, 0, 0, 2, 0, 0, 3, 1, 3, 3, 3, 3]

theorem recover_081 : pairSubgroup 81 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 81 [3, 0, 2, 1, 1, 2, 0, 0, 0, 0, 0, 2, 1, 1, 1, 2, 2, 0, 0, 0, 3, 3, 1, 1, 2, 0] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 81 [3, 0, 2, 1, 1, 2, 0, 0, 0, 0, 0, 2, 1, 1, 1, 2, 2, 0, 0, 0, 3, 3, 1, 1, 2, 0]
  · have h : pairWord 81 [2, 0, 0, 2, 1, 1, 3, 0, 0, 2, 0, 0, 2, 0, 2, 1, 1, 1, 2] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 81 [2, 0, 0, 2, 1, 1, 3, 0, 0, 2, 0, 0, 2, 0, 2, 1, 1, 1, 2]

end Sporadic.LeechRelated.HS.SmallIndex.GenerationCertificate
