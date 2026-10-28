module

public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Cartan
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Source
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Source
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.Source

/-!
# Assembly of the non-A₅ generation bound from faithful Hall branches

Reselect a minimal full module while keeping L, T, M and H fixed. Large
generation supplies genuine minimal-parabolic Cartan data. If H fixes
Ω₁Z(T), use either the Hall three-group bound or the orthogonal torus
exponent bound. If H moves Ω₁Z(T), use the Hall three-group bound after the
natural-row exclusion.

The exact source theorems discharge Hall faithfulness and both order
branches, giving the generation bound for every original H-star member.
This supplies the generation input to
`source_nonnormalReduction_of_point_generation_smallOffender`.
No later point-control, survivor or normalization conclusion is used.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
Proposition 10.2.3, printed pp.745--747.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterE
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}

/-- Faithfulness and the two independent order branches feed the exact numerical input
used by the original non-A₅ survivor assembly. -/
theorem source_nonnormalGenerationBound_of_hall_branches
    (hfaithful : SourceNonnormalHallFaithfulAt T)
    (hcentral : SourceNonnormalCentralHallAt T)
    (hmoving : SourceNonnormalMovingHallAt T) : SourceNonnormalGenerationBoundAt T := by
  intro hmany L D hn ha H hH
  by_cases hlarge : 1 < generationParameter H
  · obtain ⟨E,hE⟩ := D.exists_minimal_fullModule
    have hHE : H ∈ Chapter3.HStar (T : Subgroup G) E.maximalLocal := hH
    obtain ⟨hP,f,_,hf,d,he,hperm,_⟩ :=
      source_hstar_cartan_data_of_generation_gt_one E hHE hlarge
    have hBM := he ▸ d.hall_le
    have hHall := he ▸ d.hall
    have hfaith := hfaithful hmany L E hE hn ha H hHE hlarge d.witness.abelianGroup
      hBM hHall d.witness.abelian hperm
    have hthree (hB : IsPGroup 3 d.witness.abelianGroup) : generationParameter H ≤ 2 :=
      generationParameter_le_two_of_three_hall
        (Chapter3.sqtk_of_mem_H E.simpleQTKE hHE.1.1.1)
        (T.subtype hHE.1.1.2) hP d.witness.abelianGroup d.hall_le d.hall hB
    by_cases hZ : ⁅Stellmacher.omegaOneCenterAmbient (T : Subgroup G), H⁆ = ⊥
    · rcases hcentral hmany L E hE hn ha H hHE hlarge hZ d.witness.abelianGroup
        hBM hHall d.witness.abelian hperm hfaith with hB | hexp
      · exact hthree hB
      · exact source_hstar_generation_le_two_of_hall_exponent hHE.1.1.2 hP d hf hexp
    · exact hthree (hmoving hmany L E hE hn ha H hHE hlarge hZ d.witness.abelianGroup
        hBM hHall d.witness.abelian hperm hfaith)
  · omega

/-- The original generation consumer with its Hall-faithfulness premise discharged. -/
theorem source_nonnormalGenerationBound_of_order_branches
    (hcentral : SourceNonnormalCentralHallAt T)
    (hmoving : SourceNonnormalMovingHallAt T) : SourceNonnormalGenerationBoundAt T :=
  source_nonnormalGenerationBound_of_hall_branches source_nonnormalHallFaithful hcentral hmoving

/-- The original generation-bound application with the central Hall branch
and Hall faithfulness discharged. The moving-center source branch remains
with its existing producer and the generation-bound assembly owner. -/
theorem source_nonnormalGenerationBound_of_movingHall
    (hmoving : SourceNonnormalMovingHallAt T) : SourceNonnormalGenerationBoundAt T :=
  source_nonnormalGenerationBound_of_order_branches (source_nonnormalCentralHall T) hmoving

/-- The numerical conclusion of original 10.2.3(1) for every nonnormal,
non-A₅ fundamental setup. Hall faithfulness and both center-action branches
are discharged on the same original G and T, without further source inputs. -/
theorem source_nonnormalGenerationBound : SourceNonnormalGenerationBoundAt T :=
  source_nonnormalGenerationBound_of_movingHall (source_nonnormalMovingHall T)

end CFSG.Quasithin.Chapter10
