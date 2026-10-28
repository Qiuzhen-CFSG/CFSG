module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceGeneration.Certificates.Checks

/-!
# Five conjugates generate a group containing the exact HS carrier

The kernel-checked recovery words put the two original ATLAS generators in
each generated subgroup. The defining closure of the carrier then proves
containment, without a group-order or simplicity premise. For the outer
representatives, the conclusion retains conjugators inside HS.

Source: GM02 Proposition 5.1, HS paragraph, and equations (2.5)--(2.6).
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.SourceGeneration.Certificates
open Subgroup Theory.GroupTheory _root_.Sporadic.LeechRelated.HS

/-- Five specified HS conjugates of each marked inner or outer involution
generate a subgroup containing the actual degree-100 carrier. -/
theorem representative_generates (r : Fin 4) :
    ∃ c : Fin 5 → Carrier, generated ≤
      closure (Set.range fun i => inclusion (c i) * representative r * (inclusion (c i))⁻¹) := by
  refine ⟨conjugator r, ?_⟩
  change generated ≤ closure (Set.range (generator r))
  have hw (w : List (Fin 5)) : evalWord (generator r) w ∈ closure (Set.range (generator r)) := by
    induction w with
    | nil => exact Subgroup.one_mem _
    | cons i w ih => exact Subgroup.mul_mem _ (subset_closure ⟨i, rfl⟩) ih
  apply (closure_le _).mpr
  intro p hp
  rcases Set.mem_insert_iff.mp hp with h | h
  · rw [h, ← recover_generatorA r]
    exact hw _
  · rw [Set.mem_singleton_iff.mp h, ← recover_generatorB r]
    exact hw _

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.SourceGeneration.Certificates
