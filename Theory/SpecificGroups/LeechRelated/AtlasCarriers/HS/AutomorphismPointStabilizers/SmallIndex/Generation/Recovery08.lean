module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers.SmallIndex.Generation.Support

/-!
# Conjugate-pair recovery words, part 9

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

theorem recover_082 : pairSubgroup 82 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 82 [0, 0, 2, 1, 3, 3, 0, 2, 1, 3, 1, 2, 1, 1, 3, 1, 1, 1, 1, 2, 0, 2, 0, 3, 1, 1, 2, 2] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 82 [0, 0, 2, 1, 3, 3, 0, 2, 1, 3, 1, 2, 1, 1, 3, 1, 1, 1, 1, 2, 0, 2, 0, 3, 1, 1, 2, 2]
  · have h : pairWord 82 [1, 2, 2, 0, 2, 2, 0, 0, 3, 1, 2, 1, 1, 2, 0, 0, 2, 1, 3, 3, 0, 0] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 82 [1, 2, 2, 0, 2, 2, 0, 0, 3, 1, 2, 1, 1, 2, 0, 0, 2, 1, 3, 3, 0, 0]

theorem recover_083 : pairSubgroup 83 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 83 [0, 0, 2, 1, 2, 0, 3, 1, 2, 1, 1] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 83 [0, 0, 2, 1, 2, 0, 3, 1, 2, 1, 1]
  · have h : pairWord 83 [2, 0, 0, 3, 1, 1, 1, 2, 1, 2, 0, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 83 [2, 0, 0, 3, 1, 1, 1, 2, 1, 2, 0, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3]

theorem recover_084 : pairSubgroup 84 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 84 [2, 1, 2, 2, 1, 1, 2, 0, 0, 3, 0, 0, 0, 2] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 84 [2, 1, 2, 2, 1, 1, 2, 0, 0, 3, 0, 0, 0, 2]
  · have h : pairWord 84 [2, 1, 1, 1, 1, 3, 3, 3, 0, 2, 2, 0, 0, 0, 2, 0, 2, 2, 2, 2, 1, 2, 2] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 84 [2, 1, 1, 1, 1, 3, 3, 3, 0, 2, 2, 0, 0, 0, 2, 0, 2, 2, 2, 2, 1, 2, 2]

theorem recover_085 : pairSubgroup 85 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 85 [1, 2, 2, 2, 1, 3, 1, 1, 2, 2, 1, 3, 0, 2, 2, 2, 0, 0, 2, 2, 1] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 85 [1, 2, 2, 2, 1, 3, 1, 1, 2, 2, 1, 3, 0, 2, 2, 2, 0, 0, 2, 2, 1]
  · have h : pairWord 85 [1, 2, 2, 2, 1, 3, 3, 0, 3, 1, 2, 1, 3, 0, 0, 3, 0, 3, 1, 1, 1, 3, 1, 1, 3, 3, 0] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 85 [1, 2, 2, 2, 1, 3, 3, 0, 3, 1, 2, 1, 3, 0, 0, 3, 0, 3, 1, 1, 1, 3, 1, 1, 3, 3, 0]

theorem recover_086 : pairSubgroup 86 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 86 [2, 1, 2, 2, 2, 0, 0, 2, 2, 1, 2, 0, 3, 0, 3, 3, 1, 2, 0, 0, 0] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 86 [2, 1, 2, 2, 2, 0, 0, 2, 2, 1, 2, 0, 3, 0, 3, 3, 1, 2, 0, 0, 0]
  · have h : pairWord 86 [3, 0, 2, 2, 2, 0, 0, 2, 2, 1, 3, 3, 0, 2, 1, 3, 0, 0, 3, 0, 0] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 86 [3, 0, 2, 2, 2, 0, 0, 2, 2, 1, 3, 3, 0, 2, 1, 3, 0, 0, 3, 0, 0]

theorem recover_087 : pairSubgroup 87 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 87 [2, 1, 3, 0, 3, 3, 1, 1, 3, 1, 2, 0, 3, 1, 2, 1, 2, 2, 1, 2, 1, 2] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 87 [2, 1, 3, 0, 3, 3, 1, 1, 3, 1, 2, 0, 3, 1, 2, 1, 2, 2, 1, 2, 1, 2]
  · have h : pairWord 87 [0, 0, 2, 1, 2, 2, 0, 3, 1, 3, 3, 1, 2, 0, 0, 2, 1, 3, 1, 1] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 87 [0, 0, 2, 1, 2, 2, 0, 3, 1, 3, 3, 1, 2, 0, 0, 2, 1, 3, 1, 1]

theorem recover_088 : pairSubgroup 88 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 88 [2, 1, 2, 0, 3, 3, 0, 2, 2, 1, 2, 0, 3, 3, 0, 3, 0, 3, 1, 2, 0, 0, 0, 0, 0, 2] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 88 [2, 1, 2, 0, 3, 3, 0, 2, 2, 1, 2, 0, 3, 3, 0, 3, 0, 3, 1, 2, 0, 0, 0, 0, 0, 2]
  · have h : pairWord 88 [2, 0, 0, 2, 0, 3, 0, 2, 0, 3, 1, 3, 3, 0, 0, 0, 3, 1, 3] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 88 [2, 0, 0, 2, 0, 3, 0, 2, 0, 3, 1, 3, 3, 0, 0, 0, 3, 1, 3]

theorem recover_089 : pairSubgroup 89 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 89 [1, 3, 1, 2, 2, 2, 0, 0, 0, 3, 1, 2, 0, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 89 [1, 3, 1, 2, 2, 2, 0, 0, 0, 3, 1, 2, 0, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1]
  · have h : pairWord 89 [3, 3, 3, 3, 1, 3, 3, 0, 0, 2, 2, 2, 2, 0, 3, 3, 0, 2] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 89 [3, 3, 3, 3, 1, 3, 3, 0, 0, 2, 2, 2, 2, 0, 3, 3, 0, 2]

theorem recover_090 : pairSubgroup 90 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 90 [2, 2, 1, 3, 1, 1, 2, 0, 2, 1, 3, 1, 2, 0, 0, 0, 2, 0, 3, 0, 3, 3, 0, 0] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 90 [2, 2, 1, 3, 1, 1, 2, 0, 2, 1, 3, 1, 2, 0, 0, 0, 2, 0, 3, 0, 3, 3, 0, 0]
  · have h : pairWord 90 [2, 1, 2, 0, 2, 2, 0, 3, 0, 3, 1, 2, 1, 3, 0, 3, 1, 3, 0, 2, 2, 1, 3, 1, 1, 2, 0] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 90 [2, 1, 2, 0, 2, 2, 0, 3, 0, 3, 1, 2, 1, 3, 0, 3, 1, 3, 0, 2, 2, 1, 3, 1, 1, 2, 0]

theorem recover_091 : pairSubgroup 91 = ⊤ := by
  apply eq_top_of_generators
  · have h : pairWord 91 [0, 0, 0, 0, 3, 0, 2, 2, 0, 3, 1, 1, 2, 0, 2, 2, 1] = generator 0 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 91 [0, 0, 0, 0, 3, 0, 2, 2, 0, 3, 1, 1, 2, 0, 2, 2, 1]
  · have h : pairWord 91 [0, 0, 0, 0, 3, 3, 1, 2, 0, 3, 1, 2, 0, 3, 1, 1, 3, 1, 3, 3, 1, 2, 2, 0, 0, 2] = generator 1 := by
      apply Subtype.ext
      apply Equiv.ext
      apply OrderCertificate.allFin
      decide +kernel
    exact h ▸ pairWord_mem 91 [0, 0, 0, 0, 3, 3, 1, 2, 0, 3, 1, 2, 0, 3, 1, 1, 3, 1, 3, 3, 1, 2, 2, 0, 0, 2]

end Sporadic.LeechRelated.HS.SmallIndex.GenerationCertificate
