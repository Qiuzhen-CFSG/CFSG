module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.BlockCase.FixedSpace
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Contracts

/-!
# Recognition of the corank-two factor in the E.6.7 decomposition

Once the actual overgroup is identified with an E.6.7 factor, its fixed
space of corank two excludes both alternating module types by clause (2).
Clause (3) bounds the field exponent by two; the definition of an even
rank-one block bounds it below by two. Thus its literal module is the
natural SL₂(4) module. Identification with a decomposition factor and the
characteristic-two hypothesis needed to obtain that decomposition remain
separate obligations.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.7,
printed p.246, as applied in E.6.23, printed p.254.
-/

public section

open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.BlockCase
open InvariantSubspaces.BlockSelection

variable {G : Type*} [Group G] {Q M V A H : Subgroup G}

/-- E.6.7 distinguishes the two degree-four modules using their actual V-actions. -/
theorem factor_naturalFour_of_corank_two (d : E67Decomposition Q M V A H)
    (hA : subgroupCorank V A = 2) (i : Fin d.count)
    (hfixed : subgroupCorank V (V ⊓ centralizer (d.block i : Set G)) = 2) :
    ChapterC.IsL2EvenBlock (d.block i) 2 := by
  rcases d.type i with ⟨n, hn⟩ | hthree | hfive
  · obtain ⟨D, _, _, _, _, _, _, _, _, hbound⟩ := d.rankOne i n hn
    rw [hA] at hbound
    have hn2 : n = 2 := by have := hn.1; omega
    simpa only [hn2] using hn
  · have hc := (d.alternating i 3 hthree).1
    omega
  · have hc := (d.alternating i 5 hfive).1
    omega

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.BlockCase
