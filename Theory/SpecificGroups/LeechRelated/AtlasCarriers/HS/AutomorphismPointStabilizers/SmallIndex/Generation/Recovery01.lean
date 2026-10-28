module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers.SmallIndex.Generation.Support

/-!
# Conjugate-pair recovery words, part 2

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

theorem recover_012 : pairSubgroup 12 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 12 [0, 3, 0, 0, 2, 2, 1, 3, 0, 3, 3, 3, 1, 3, 1, 2, 1, 1, 2, 1, 2] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 12 [0, 3, 0, 0, 2, 2, 1, 3, 0, 3, 3, 3, 1, 3, 1, 2, 1, 1, 2, 1, 2]
  · have h : pairWord 12 [1, 3, 3, 1, 1, 1, 2, 2, 0, 3, 0, 2, 0, 0, 3, 0, 2, 1] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 12 [1, 3, 3, 1, 1, 1, 2, 2, 0, 3, 0, 2, 0, 0, 3, 0, 2, 1]

theorem recover_013 : pairSubgroup 13 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 13 [0, 3, 0, 3, 3, 3, 3, 0, 0, 0, 2, 2, 1, 3, 1, 3, 0, 2, 0, 2, 2, 1, 3, 3, 1, 1, 1] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 13 [0, 3, 0, 3, 3, 3, 3, 0, 0, 0, 2, 2, 1, 3, 1, 3, 0, 2, 0, 2, 2, 1, 3, 3, 1, 1, 1]
  · have h : pairWord 13 [0, 0, 3, 1, 2, 0, 0, 2, 1, 2, 2, 1, 1, 3, 3, 3, 1] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 13 [0, 0, 3, 1, 2, 0, 0, 2, 1, 2, 2, 1, 1, 3, 3, 3, 1]

theorem recover_014 : pairSubgroup 14 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 14 [0, 0, 3, 0, 3, 1, 2, 0, 0, 0, 0, 0, 0, 3, 3, 1, 2] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 14 [0, 0, 3, 0, 3, 1, 2, 0, 0, 0, 0, 0, 0, 3, 3, 1, 2]
  · have h : pairWord 14 [2, 1, 1, 2, 2, 2, 0, 3, 3, 3, 1, 1, 1, 3, 1, 3, 0, 0, 0, 2, 2] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 14 [2, 1, 1, 2, 2, 2, 0, 3, 3, 3, 1, 1, 1, 3, 1, 3, 0, 0, 0, 2, 2]

theorem recover_015 : pairSubgroup 15 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 15 [1, 2, 1, 2, 2, 0, 0, 3, 1, 2, 0, 3, 1, 2, 0, 3, 1, 3, 0, 3, 0, 3] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 15 [1, 2, 1, 2, 2, 0, 0, 3, 1, 2, 0, 3, 1, 2, 0, 3, 1, 3, 0, 3, 0, 3]
  · have h : pairWord 15 [1, 1, 3, 3, 0, 3, 0, 2, 1, 3, 3, 0, 3, 3, 3, 0, 2, 0, 3, 3, 0, 0, 2, 1, 1, 1] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 15 [1, 1, 3, 3, 0, 3, 0, 2, 1, 3, 3, 0, 3, 3, 3, 0, 2, 0, 3, 3, 0, 0, 2, 1, 1, 1]

theorem recover_016 : pairSubgroup 16 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 16 [0, 0, 0, 0, 0, 3, 1, 3, 3, 0, 2, 2, 0, 2, 2, 1, 1, 1] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 16 [0, 0, 0, 0, 0, 3, 1, 3, 3, 0, 2, 2, 0, 2, 2, 1, 1, 1]
  · have h : pairWord 16 [1, 1, 1, 2, 0, 2, 2, 0, 3, 0, 2, 0, 2, 1, 1, 1, 1, 1, 2, 2, 0, 0, 3, 0, 0, 3] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 16 [1, 1, 1, 2, 0, 2, 2, 0, 3, 0, 2, 0, 2, 1, 1, 1, 1, 1, 2, 2, 0, 0, 3, 0, 0, 3]

theorem recover_017 : pairSubgroup 17 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 17 [1, 1, 1, 2, 1, 2, 1, 3, 0, 0, 0, 0, 0, 2, 1, 1] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 17 [1, 1, 1, 2, 1, 2, 1, 3, 0, 0, 0, 0, 0, 2, 1, 1]
  · have h : pairWord 17 [3, 3, 1, 3, 1, 1, 3, 0, 3, 1, 3, 3, 0, 2, 0, 0, 2, 0, 0, 0, 2] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 17 [3, 3, 1, 3, 1, 1, 3, 0, 3, 1, 3, 3, 0, 2, 0, 0, 2, 0, 0, 0, 2]

theorem recover_018 : pairSubgroup 18 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 18 [1, 3, 3, 3, 0, 3, 3, 3, 0, 0, 2, 1, 1, 3, 3, 0, 3] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 18 [1, 3, 3, 3, 0, 3, 3, 3, 0, 0, 2, 1, 1, 3, 3, 0, 3]
  · have h : pairWord 18 [1, 3, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 0, 2, 2, 0, 2, 0] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 18 [1, 3, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 0, 2, 2, 0, 2, 0]

theorem recover_019 : pairSubgroup 19 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 19 [1, 3, 3, 0, 2, 2, 1, 3, 1, 1, 1, 2, 2, 0, 3, 0, 3, 0, 0, 3, 0, 2] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 19 [1, 3, 3, 0, 2, 2, 1, 3, 1, 1, 1, 2, 2, 0, 3, 0, 3, 0, 0, 3, 0, 2]
  · have h : pairWord 19 [2, 0, 3, 3, 1, 2, 2, 0, 2, 2, 0, 2, 0, 3, 0, 2, 1, 1, 1] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 19 [2, 0, 3, 3, 1, 2, 2, 0, 2, 2, 0, 2, 0, 3, 0, 2, 1, 1, 1]

theorem recover_020 : pairSubgroup 20 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 20 [2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 3, 0, 0, 2, 1, 1, 2, 2, 2, 1, 1] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 20 [2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 3, 0, 0, 2, 1, 1, 2, 2, 2, 1, 1]
  · have h : pairWord 20 [1, 2, 1, 1, 3, 0, 0, 0, 2, 2, 2, 2, 2, 1, 1, 2, 0, 0, 0, 0, 2] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 20 [1, 2, 1, 1, 3, 0, 0, 0, 2, 2, 2, 2, 2, 1, 1, 2, 0, 0, 0, 0, 2]

theorem recover_021 : pairSubgroup 21 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 21 [0, 0, 0, 3, 3, 1, 1, 3, 1, 2, 0, 0, 2, 2, 1, 3, 3, 0] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 21 [0, 0, 0, 3, 3, 1, 1, 3, 1, 2, 0, 0, 2, 2, 1, 3, 3, 0]
  · have h : pairWord 21 [0, 0, 2, 2, 0, 2, 1, 2, 1, 1, 2, 0, 3, 0, 2, 0, 0, 0, 0, 3] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 21 [0, 0, 2, 2, 0, 2, 1, 2, 1, 1, 2, 0, 3, 0, 2, 0, 0, 0, 0, 3]

end Sporadic.LeechRelated.HS.SmallIndex.GenerationCertificate
