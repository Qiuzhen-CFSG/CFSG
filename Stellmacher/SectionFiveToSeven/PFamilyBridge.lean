module

public import Stellmacher.SectionFiveToSeven.Defs

/-!
# Identifying the Section 3 and Section 5 local families

The notation for Stellmacher's local family is introduced once in Section 3
and restated for the hypotheses used in Sections 5--7.  This module proves that
the two formal definitions have identical membership.  The proof converts the
equivalent descriptions of a Sylow 2-subgroup inside an ambient subgroup and
of the unique maximal subgroup containing it; all remaining clauses agree
definitionally.  This bridge lets later proofs invoke the Section 3 results
without duplicating their local-family hypotheses.

Source: the definition of `𝒫(U,S)` in Section 3 of
`refs/latex/stellmacher-n-group.tex` and its continued use in Sections 5--7.
-/

namespace Stellmacher.SectionsFiveToSeven

universe u

variable {G : Type u} [Group G]

private theorem isSylowTwoIn_iff_isSylowSubgroupIn (S P : Subgroup G) :
    IsSylowTwoIn S P ↔ Stellmacher.IsSylowSubgroupIn S P := by
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    obtain ⟨T, rfl⟩ := h
    exact Subgroup.map_subtype_le _

private theorem hasUniqueMaximalOver_iff_isUniqueMaximalContaining
    (S P : Subgroup G) :
    HasUniqueMaximalOver S P ↔
      Stellmacher.IsUniqueMaximalContaining S P := by
  constructor
  · rintro ⟨hSP, M, hMmax, hSM, huniq⟩
    refine ⟨M, hMmax, ?_, ?_⟩
    · have hmap : (S.subgroupOf P).map P.subtype ≤ M.map P.subtype :=
        Subgroup.map_mono hSM
      simpa [Subgroup.map_subgroupOf_eq_of_le hSP] using hmap
    · intro M' hM'max hSM'
      apply huniq M' hM'max
      apply Subgroup.map_subtype_le_map_subtype.mp
      simpa [Subgroup.map_subgroupOf_eq_of_le hSP] using hSM'
  · rintro ⟨M, hMmax, hSM, huniq⟩
    have hSP : S ≤ P := hSM.trans (Subgroup.map_subtype_le M)
    refine ⟨hSP, M, hMmax, ?_, ?_⟩
    · apply Subgroup.map_subtype_le_map_subtype.mp
      simpa [Subgroup.map_subgroupOf_eq_of_le hSP] using hSM
    · intro M' hM'max hSM'
      apply huniq M' hM'max
      have hmap : (S.subgroupOf P).map P.subtype ≤ M'.map P.subtype :=
        Subgroup.map_mono hSM'
      simpa [Subgroup.map_subgroupOf_eq_of_le hSP] using hmap

/-- The Section 5--7 family `PFamily` is the Section 3 family `PSet`.
The equivalence is stated pointwise so it rewrites membership hypotheses in
either direction without exposing the bookkeeping lemmas above. -/
public theorem pFamily_iff_pSet (U S P : Subgroup G) :
    P ∈ PFamily U S ↔ P ∈ Stellmacher.SectionThree.PSet U S := by
  simp only [PFamily, IsPMember, IsLMember,
    Stellmacher.SectionThree.PSet, Stellmacher.SectionThree.LSet,
    Set.mem_ofPred_eq, twoCoreIn, Stellmacher.twoCoreAmbient]
  rw [isSylowTwoIn_iff_isSylowSubgroupIn,
    hasUniqueMaximalOver_iff_isUniqueMaximalContaining]

end Stellmacher.SectionsFiveToSeven
