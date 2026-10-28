module

public import CFSG.Quasithin.ChapterI.Section04To05.C3Recognition.SourceDistanceGeometry
public import CFSG.Quasithin.ChapterI.Section04To05.Residues.NonsingularTriples

/-!
# C₃ recognition from the original marked point residues

All global incidence, kernel and core inputs to reconstruction now follow
from the bare D-system and the three literal local polar-residue facts.
The separate marked-quotient producer supplies exactly those local facts;
no global recognition or geometry conclusion remains as a premise here.
-/

public noncomputable section
namespace Quasithin.I5.C3Recognition
open Theory.SpecificGroups.SymplecticSix
variable {G : Type*} [Group G] (S : DSystem .C3 G)

def equivSp6_of_local_polar_facts (d : S.LocalPolarFacts) : G ≃* Sp (ZMod 2) :=
  equivSp6_of_source_nonsingular_triples S d (fun _ _ h => S.nonsingular_one_or_all d h)

end Quasithin.I5.C3Recognition
