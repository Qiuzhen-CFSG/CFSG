module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Elementary
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Generation
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Splitting
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Triple

/-!
# Initial natural-section assembly

The complete natural-section output of (4.3.1)(iii) implies the local
conjugate-generation assertion (iv), including its kernel-containment step.
The radius quotient, triple commutator and dual-module splitting are proved
in the imported natural-section branches. The final constructor below retains
the source's order-four hypothesis as its only numerical premise.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.1)(iii)--(iv), pp.882--883.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial.Natural
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : Geometry R}

/-- Assemble the representation and generation outputs once (iii) has been proved.
This theorem proves (iv); it does not construct the assumed natural section. -/
theorem sectionFacts_of_naturalSection (source : LocalSource L R)
    (hb : 2 < geometry.b R) (p : Counterexample geometry)
    (s : NaturalSectionAt p.a (V R p.a) (Z R p.a)) : Nonempty (SectionFacts p) := by
  exact ⟨{
    natural_section := s
    moving_generation := moving_generation_of_naturalSection source geometry hb p.a p.color_a s }⟩

/-- Construct the complete natural section and its moving-generation clause
from the order-four numerical stage.  The triple commutator is proved in the
actual free amalgam and then supplied to the natural splitting transport. -/
theorem sectionFacts_of_radius_card_four (source : LocalSource L R)
    (geometry : Geometry R) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry) (p : Counterexample geometry)
    (hfour : Nat.card (radiusCommutator p.a p.a') = 4) :
    Nonempty (SectionFacts p) := by
  have htriple := Triple.radius_triple_commutator source geometry hb modules p hfour
  obtain ⟨s⟩ := Splitting.naturalSectionAt_of_triple
    source geometry hb modules p hfour htriple
  exact sectionFacts_of_naturalSection source hb p s

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial.Natural
