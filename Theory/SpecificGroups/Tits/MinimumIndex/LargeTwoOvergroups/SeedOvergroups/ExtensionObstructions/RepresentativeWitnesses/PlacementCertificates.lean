module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.Cases
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.PlacementCertificates.Checks

/-!
# Complete placement witnesses for the finite seed extensions

Every candidate selected by the unchanged `.place` branch belongs to an
available checked rectangle. Its literal place contains the seed, and subgroup
multiplication expands the rectangle's anchor to the requested representative.
This constructs precisely the first disjunct of `RepresentativeWitness`.

The proof uses no seed catalogue, Sylow factorization, fixed-place exhaustion,
or geometry coverage. The parent retains assembly of the other two branches.
Source: Parrott (1972), §5, p.683, and the original checked finite data described
in `PlacementCertificates/source/README.md`.
-/

public section
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeCertificates
open Placement

/-- Every placement case has an actual listed place containing both its seed
and its literal representative. -/
theorem placementWitnesses (i : Fin 122) (a b : Fin 32) (c : Fin 15) (h : witnessCase i a b c = .place) :
    RepresentativeWitness i a b ⟨c.val + 3, by omega⟩ := by
  have hp : (placeMasks (placeSelector i)).testBit (candidateIndex a b c) = true := by
    unfold witnessCase at h
    split at h
    · cases h
    · split at h
      · assumption
      · cases h
  have hc : (coverMask i).testBit (candidateIndex a b c) = true := by
    have he := congrArg (fun n : Nat => n.testBit (candidateIndex a b c)) (mask_coverage i)
    simpa only [Nat.testBit_and, hp, Bool.true_and] using he
  obtain ⟨m, hm, hbit⟩ := (maskUnion_bit _ _).mp hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hm
  obtain ⟨hdata, hfilter⟩ := List.mem_filter.mp hd
  have hd' : d.1.pattern = seedTransversalPattern i ∧ d.1.placeId ∈ placeIds i := by
    simpa only [decide_eq_true_eq] using hfilter
  have hchecked := List.all_eq_true.mp (certificates_checked (seedTransversalPattern i)) d hdata
  have htests : tileTest d.1 = true ∧ d.2 = tileMask d.1 := by
    simpa only [certificateTest, Bool.and_eq_true, decide_eq_true_eq] using hchecked
  rw [htests.2] at hbit
  obtain ⟨ha, hb, hcoset⟩ := tileMask_sound d.1 a b c hbit
  have hmem := tileTest_sound d.1 htests.1 a b ha hb
  refine Or.inl ⟨d.1.placeId, hd'.2, seed_le_place i d.1.placeId hd'.2, ?_⟩
  rw [hd'.1, ← hcoset] at hmem
  exact hmem

end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeCertificates
