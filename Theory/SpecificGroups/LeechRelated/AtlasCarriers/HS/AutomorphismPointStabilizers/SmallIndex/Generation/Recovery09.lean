module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers.SmallIndex.Generation.Support

/-!
# Conjugate-pair recovery words, part 10

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

theorem recover_092 : pairSubgroup 92 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 92 [1, 1, 3, 1, 2, 0, 2, 0, 0, 0, 2, 1, 3, 1, 3, 1, 3, 3, 1, 1, 3, 3, 0, 3, 1, 1] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 92 [1, 1, 3, 1, 2, 0, 2, 0, 0, 0, 2, 1, 3, 1, 3, 1, 3, 3, 1, 1, 3, 3, 0, 3, 1, 1]
  · have h : pairWord 92 [1, 3, 1, 3, 0, 2, 0, 0, 3, 1, 1, 3, 1, 1, 3, 3, 3, 0, 0, 0, 0, 3, 3, 3, 3, 3, 0] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 92 [1, 3, 1, 3, 0, 2, 0, 0, 3, 1, 1, 3, 1, 1, 3, 3, 3, 0, 0, 0, 0, 3, 3, 3, 3, 3, 0]

theorem recover_093 : pairSubgroup 93 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 93 [3, 1, 1, 2, 0, 3, 0, 3, 3, 0, 2, 2, 0, 0, 0, 2, 1, 3, 3] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 93 [3, 1, 1, 2, 0, 3, 0, 3, 3, 0, 2, 2, 0, 0, 0, 2, 1, 3, 3]
  · have h : pairWord 93 [2, 1, 1, 3, 1, 1, 2, 2, 0, 2, 1, 3, 0, 0, 2] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 93 [2, 1, 1, 3, 1, 1, 2, 2, 0, 2, 1, 3, 0, 0, 2]

theorem recover_094 : pairSubgroup 94 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 94 [0, 3, 1, 3, 3, 0, 2, 2, 2, 1, 1, 2, 2, 0, 0, 2, 2, 2, 2, 1, 1] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 94 [0, 3, 1, 3, 3, 0, 2, 2, 2, 1, 1, 2, 2, 0, 0, 2, 2, 2, 2, 1, 1]
  · have h : pairWord 94 [2, 2, 1, 1, 2, 0, 2, 1, 2, 1, 1, 1, 3, 0] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 94 [2, 2, 1, 1, 2, 0, 2, 1, 2, 1, 1, 1, 3, 0]

theorem recover_095 : pairSubgroup 95 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 95 [3, 0, 0, 0, 3, 0, 2, 2, 1, 2, 0, 2, 2, 0, 0, 0, 0, 2] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 95 [3, 0, 0, 0, 3, 0, 2, 2, 1, 2, 0, 2, 2, 0, 0, 0, 0, 2]
  · have h : pairWord 95 [0, 2, 1, 1, 2, 1, 3, 3, 0, 0, 3, 0, 0, 0, 2, 0] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 95 [0, 2, 1, 1, 2, 1, 3, 3, 0, 0, 3, 0, 0, 0, 2, 0]

theorem recover_096 : pairSubgroup 96 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 96 [1, 3, 0, 2, 0, 0, 2, 2, 1, 2, 2, 2, 2, 2, 0, 2, 1, 2, 0, 3, 1, 2, 1, 3, 1] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 96 [1, 3, 0, 2, 0, 0, 2, 2, 1, 2, 2, 2, 2, 2, 0, 2, 1, 2, 0, 3, 1, 2, 1, 3, 1]
  · have h : pairWord 96 [3, 1, 3, 3, 3, 3, 0, 3, 0, 3, 0, 2, 0, 3, 3, 1] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 96 [3, 1, 3, 3, 3, 3, 0, 3, 0, 3, 0, 2, 0, 3, 3, 1]

theorem recover_097 : pairSubgroup 97 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 97 [3, 3, 0, 2, 2, 0, 2, 0, 3, 3, 1, 2, 0, 3, 0, 0, 0, 0, 3, 3, 3, 1, 1, 1, 1, 1, 1, 3, 1] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 97 [3, 3, 0, 2, 2, 0, 2, 0, 3, 3, 1, 2, 0, 3, 0, 0, 0, 0, 3, 3, 3, 1, 1, 1, 1, 1, 1, 3, 1]
  · have h : pairWord 97 [2, 2, 2, 0, 2, 0, 3, 3, 3, 0, 2, 0, 3, 3, 0, 0, 3, 3, 0, 2, 2, 0, 2] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 97 [2, 2, 2, 0, 2, 0, 3, 3, 3, 0, 2, 0, 3, 3, 0, 0, 3, 3, 0, 2, 2, 0, 2]

theorem recover_098 : pairSubgroup 98 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 98 [3, 3, 3, 0, 3, 3, 0, 0, 3, 0, 0, 2, 2, 2, 1, 2, 2, 2, 0, 0, 0, 0, 2, 1, 2, 2, 1, 2, 0, 3, 3, 0] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 98 [3, 3, 3, 0, 3, 3, 0, 0, 3, 0, 0, 2, 2, 2, 1, 2, 2, 2, 0, 0, 0, 0, 2, 1, 2, 2, 1, 2, 0, 3, 3, 0]
  · have h : pairWord 98 [0, 0, 3, 3, 3, 3, 0, 0, 2, 0, 0, 0, 0, 3, 0, 3, 0, 2, 2, 1, 3, 1, 3, 0] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 98 [0, 0, 3, 3, 3, 3, 0, 0, 2, 0, 0, 0, 0, 3, 0, 3, 0, 2, 2, 1, 3, 1, 3, 0]

theorem recover_099 : pairSubgroup 99 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 99 [3, 0, 3, 3, 0, 3, 0, 3, 1, 1, 3, 1, 2, 0, 3, 0, 0, 2, 1] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 99 [3, 0, 3, 3, 0, 3, 0, 3, 1, 1, 3, 1, 2, 0, 3, 0, 0, 2, 1]
  · have h : pairWord 99 [3, 0, 3, 3, 0, 3, 0, 2, 0, 3, 1, 3, 3, 3, 1, 3, 0, 3, 3, 1, 2, 0] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 99 [3, 0, 3, 3, 0, 3, 0, 2, 0, 3, 1, 3, 3, 3, 1, 3, 0, 3, 3, 1, 2, 0]

theorem recover_100 : pairSubgroup 100 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 100 [2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 3, 1, 2, 2, 0, 3, 0, 0, 0, 2] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 100 [2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 3, 1, 2, 2, 0, 3, 0, 0, 0, 2]
  · have h : pairWord 100 [0, 0, 0, 3, 1, 3, 1, 2, 0, 2, 0, 3, 0, 2, 0, 3, 0] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 100 [0, 0, 0, 3, 1, 3, 1, 2, 0, 2, 0, 3, 0, 2, 0, 3, 0]

theorem recover_101 : pairSubgroup 101 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 101 [3, 0, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 1, 3] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 101 [3, 0, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 1, 3]
  · have h : pairWord 101 [3, 1, 1, 2, 1, 3, 0, 2, 2, 2, 1, 1, 1, 3, 3, 0, 0, 0, 2, 1, 2, 0] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 101 [3, 1, 1, 2, 1, 3, 0, 2, 2, 2, 1, 1, 1, 3, 3, 0, 0, 0, 2, 1, 2, 0]

end Sporadic.LeechRelated.HS.SmallIndex.GenerationCertificate
