module
public import CFSG.Quasithin.ChapterA.Section04.SourceChains
public import CFSG.Quasithin.Chapter1.Section02.Adequate.Faithful
public import CFSG.Quasithin.Chapter1.Section03.Terminal.Modules
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
/-!
# Literal Chapter1 applications of the proved A.4.10 chain theorem

The same A.4.10 theorem supplies both existing source interfaces, retaining
the original Sylow subgroups and section centralizers. In1.3.9(2), the
genuine characteristic-two theorem supplies the other universal input;
thus an actual faithful radical in the T-orbit of B proves B faithful.

Source: Aschbacher--Smith A.4.10, p.60, and1.3.9(2), p.514.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section04.SourceChains
variable {G : Type*} [Group G] [Finite G]

theorem adequate_source : Chapter1.Section02.Adequate.A410EarlierResult G :=
  source_A410

theorem terminal_source : Chapter1.Terminal.SourceA410 G :=
  source_A410

end CFSG.Quasithin.ChapterA.Section04.SourceChains

namespace CFSG.Quasithin.Chapter1.Terminal
open ChapterA.Section04
universe u
variable {G : Type u} [Group G] [Finite G]

theorem lemma_1_3_9_two_source {κ : GroupClass.{u}} (hG : IsSimpleQTKE κ G)
    (T : Sylow 2 G) {X B : Subgroup G} (hX : X ∈ XiF G T) (hB : B ∈ L G T)
    (hXB : X ≤ componentOrbit B T) :
    signalizerModule X (twoSectionCentralizer X ((T : Subgroup G) ⊓ componentOrbit B T)) ≤
        intrinsicSignalizerModule (componentOrbit B T) ∧
      B ∈ MainForward.faithfulLocalComponents T :=
  lemma_1_3_9_two_of_A_4_10 T (lemma_1_1_4_6 T (hG.evenCharacteristic T))
    SourceChains.terminal_source hX hB hXB

end CFSG.Quasithin.Chapter1.Terminal
