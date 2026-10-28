module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers.SmallIndex.Generation.Support

/-!
# Conjugate-pair recovery words, part 5

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

theorem recover_042 : pairSubgroup 42 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 42 [1, 1, 3, 3, 3, 3, 3, 1, 3, 3, 0, 3, 0, 2, 1, 1, 2, 2, 0, 2, 2, 0, 3] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 42 [1, 1, 3, 3, 3, 3, 3, 1, 3, 3, 0, 3, 0, 2, 1, 1, 2, 2, 0, 2, 2, 0, 3]
  · have h : pairWord 42 [1, 2, 2, 2, 1, 1, 1, 1, 3, 0, 0, 3, 1, 3, 0, 3, 0, 0, 2, 1] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 42 [1, 2, 2, 2, 1, 1, 1, 1, 3, 0, 0, 3, 1, 3, 0, 3, 0, 0, 2, 1]

theorem recover_043 : pairSubgroup 43 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 43 [2, 2, 0, 0, 0, 3, 1, 2, 0, 3, 1, 3, 0, 0, 3, 0, 3, 0, 0, 2, 1, 1, 3, 1, 3, 3, 1] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 43 [2, 2, 0, 0, 0, 3, 1, 2, 0, 3, 1, 3, 0, 0, 3, 0, 3, 0, 0, 2, 1, 1, 3, 1, 3, 3, 1]
  · have h : pairWord 43 [2, 2, 0, 0, 0, 3, 1, 2, 2, 1, 3, 3, 1, 3, 1, 1, 3, 1, 3, 3, 1, 1, 2, 0, 2, 2, 1, 3, 0, 2, 1, 3, 0, 0] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 43 [2, 2, 0, 0, 0, 3, 1, 2, 2, 1, 3, 3, 1, 3, 1, 1, 3, 1, 3, 3, 1, 1, 2, 0, 2, 2, 1, 3, 0, 2, 1, 3, 0, 0]

theorem recover_044 : pairSubgroup 44 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 44 [0, 0, 2, 1, 2, 1, 3, 3, 0, 0, 0, 2, 2, 0, 2, 1, 1, 1, 3, 0, 0, 0, 3, 3, 0] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 44 [0, 0, 2, 1, 2, 1, 3, 3, 0, 0, 0, 2, 2, 0, 2, 1, 1, 1, 3, 0, 0, 0, 3, 3, 0]
  · have h : pairWord 44 [2, 2, 1, 2, 1, 3, 1, 2, 0, 0, 2, 2, 1, 1, 2, 0] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 44 [2, 2, 1, 2, 1, 3, 1, 2, 0, 0, 2, 2, 1, 1, 2, 0]

theorem recover_045 : pairSubgroup 45 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 45 [2, 0, 3, 1, 1, 2, 1, 3, 3, 3, 0, 3, 0, 0, 0, 2] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 45 [2, 0, 3, 1, 1, 2, 1, 3, 3, 3, 0, 3, 0, 0, 0, 2]
  · have h : pairWord 45 [2, 0, 2, 0, 0, 0, 2, 2, 0, 3, 1, 3, 1, 2, 2, 0, 0, 0, 3, 0, 3, 3, 0, 2, 0, 2, 0, 0] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 45 [2, 0, 2, 0, 0, 0, 2, 2, 0, 3, 1, 3, 1, 2, 2, 0, 0, 0, 3, 0, 3, 3, 0, 2, 0, 2, 0, 0]

theorem recover_046 : pairSubgroup 46 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 46 [2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 0, 3] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 46 [2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 0, 3]
  · have h : pairWord 46 [2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 0, 0, 2, 0, 3, 1, 2, 2, 2] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 46 [2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 0, 0, 2, 0, 3, 1, 2, 2, 2]

theorem recover_047 : pairSubgroup 47 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 47 [3, 1, 2, 1, 3, 1, 3, 3, 0, 3, 0, 2, 2, 0, 2, 0, 2, 1, 3, 0, 3, 1, 1, 3, 3, 0] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 47 [3, 1, 2, 1, 3, 1, 3, 3, 0, 3, 0, 2, 2, 0, 2, 0, 2, 1, 3, 0, 3, 1, 1, 3, 3, 0]
  · have h : pairWord 47 [1, 2, 1, 3, 0, 0, 3, 1, 3, 1, 3, 3, 1, 2, 1, 2, 2, 0, 2, 0, 3, 0, 2] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 47 [1, 2, 1, 3, 0, 0, 3, 1, 3, 1, 3, 3, 1, 2, 1, 2, 2, 0, 2, 0, 3, 0, 2]

theorem recover_048 : pairSubgroup 48 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 48 [1, 3, 3, 3, 0, 0, 0, 3, 0, 3, 0, 3, 0, 3, 3, 0, 0, 2, 0, 3, 0, 0, 0] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 48 [1, 3, 3, 3, 0, 0, 0, 3, 0, 3, 0, 3, 0, 3, 3, 0, 0, 2, 0, 3, 0, 0, 0]
  · have h : pairWord 48 [0, 0, 3, 1, 3, 3, 3, 3, 0, 0, 0, 3, 3, 1, 3, 3, 3, 0, 0] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 48 [0, 0, 3, 1, 3, 3, 3, 3, 0, 0, 0, 3, 3, 1, 3, 3, 3, 0, 0]

theorem recover_049 : pairSubgroup 49 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 49 [3, 1, 2, 1, 2, 0, 2, 0, 0, 3, 3, 1, 2, 2, 2, 2, 0, 3, 1, 1, 1, 1, 1, 2, 2, 2] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 49 [3, 1, 2, 1, 2, 0, 2, 0, 0, 3, 3, 1, 2, 2, 2, 2, 0, 3, 1, 1, 1, 1, 1, 2, 2, 2]
  · have h : pairWord 49 [1, 2, 1, 2, 2, 2, 0, 0, 3, 0, 3, 0, 3, 0, 2, 0, 2, 1, 3, 1, 3, 0, 3, 0, 2] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 49 [1, 2, 1, 2, 2, 2, 0, 0, 3, 0, 3, 0, 3, 0, 2, 0, 2, 1, 3, 1, 3, 0, 3, 0, 2]

theorem recover_050 : pairSubgroup 50 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 50 [3, 1, 3, 1, 3, 3, 1, 3, 1, 3, 1, 1, 2, 2, 0, 3, 3, 0, 0, 3, 3] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 50 [3, 1, 3, 1, 3, 3, 1, 3, 1, 3, 1, 1, 2, 2, 0, 3, 3, 0, 0, 3, 3]
  · have h : pairWord 50 [0, 3, 3, 1, 3, 1, 3, 3, 1, 3, 1, 3, 0, 2, 2, 0, 3, 1, 2, 1, 3, 3, 0] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 50 [0, 3, 3, 1, 3, 1, 3, 3, 1, 3, 1, 3, 0, 2, 2, 0, 3, 1, 2, 1, 3, 3, 0]

theorem recover_051 : pairSubgroup 51 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 51 [3, 3, 1, 2, 2, 2, 1, 3, 3, 1, 1, 1, 1, 1, 2, 2, 1, 3, 0, 3, 1, 1, 2, 0, 3, 1, 2] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 51 [3, 3, 1, 2, 2, 2, 1, 3, 3, 1, 1, 1, 1, 1, 2, 2, 1, 3, 0, 3, 1, 1, 2, 0, 3, 1, 2]
  · have h : pairWord 51 [3, 0, 2, 2, 0, 3, 3, 0, 3, 3, 0, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 51 [3, 0, 2, 2, 0, 3, 3, 0, 3, 3, 0, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2]

end Sporadic.LeechRelated.HS.SmallIndex.GenerationCertificate
