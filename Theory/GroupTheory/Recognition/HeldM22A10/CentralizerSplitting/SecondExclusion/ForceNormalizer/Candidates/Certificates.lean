module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Candidates.Generators
public import Theory.GroupTheory.NormalizerPCoreWitness

/-!
# Independent finite obligations for the second Held candidates

The 45 proposed representatives are partitioned into 25 characteristic-kernel
checks, 19 normalizer two-core witnesses, and the named exceptional subgroup.
Only the partition and its logical use are proved here. Characteristicity and
the witnesses are explicit outstanding inputs, not assumed model facts.

A witness outside a centric subgroup whose action belongs to the two-core of
its full automorphism group contradicts intrinsic radicality. Consequently the
two independent certificate families imply `RepresentativeProperty`.

Source: the proposed finite calculation for Huppert--Blackburn III,
XII.1.18(b), printed p.314; see `source/README.md` for discovery provenance.
-/

namespace Theory.GroupTheory.HeldM22A10.SecondExclusion.ForceNormalizer.Candidates
open Subgroup

/-- Entries assigned to characteristicity checks. The assignment asserts no
automorphism property until `CharacteristicChecks` is proved. -/
@[expose] public def characteristicIndex : Fin 25 → Fin 45 :=
  ![0, 1, 3, 5, 8, 11, 12, 15, 17, 18, 21, 22, 24, 25, 26, 28, 29,
    30, 31, 32, 37, 38, 39, 41, 44]

/-- Entries assigned to outside normalizer two-core witnesses. -/
@[expose] public def obstructionIndex : Fin 19 → Fin 45 :=
  ![2, 4, 6, 7, 9, 10, 13, 14, 16, 19, 20, 23, 27, 33, 34, 35, 36, 42, 43]

/-- The proposed checks cover every representative, including the named
exceptional entry; this is only a finite index identity. -/
public theorem certificate_cases (i : Fin 45) :
    (∃ j, characteristicIndex j = i) ∨
    (∃ j, obstructionIndex j = i) ∨ i = 40 := by
  have h : ∀ k : Fin 45, (∃ j, characteristicIndex j = k) ∨
      (∃ j, obstructionIndex j = k) ∨ k = 40 := by decide +kernel
  exact h i

/-- Characteristicity is intrinsic to each actual representative. -/
@[expose] public def CharacteristicChecks : Prop :=
  ∀ j : Fin 25, (kernel.subgroupOf (representative (characteristicIndex j))).Characteristic

/-- An actual element of the Sylow normalizer, outside the representative,
whose action lies in the two-core of its full automorphism group. -/
@[expose] public def ObstructionChecks : Prop :=
  ∀ j : Fin 19, (representative (obstructionIndex j)).HasPCoreNormalizerWitness 2

/-- Two independently supplied finite certificate families prove the exact
representative assertion. Neither family is supplied by this theorem. -/
public theorem representativeProperty_of_certificates
    (hchar : CharacteristicChecks) (hobs : ObstructionChecks) : RepresentativeProperty := by
  intro i hc hr
  rcases certificate_cases i with ⟨j, rfl⟩ | ⟨j, rfl⟩ | rfl
  · exact Or.inl (hchar j)
  · exact (not_hasPCoreNormalizerWitness_of_intrinsic_radical _ hc hr (hobs j)).elim
  · exact Or.inr representative_exceptional

end Theory.GroupTheory.HeldM22A10.SecondExclusion.ForceNormalizer.Candidates
