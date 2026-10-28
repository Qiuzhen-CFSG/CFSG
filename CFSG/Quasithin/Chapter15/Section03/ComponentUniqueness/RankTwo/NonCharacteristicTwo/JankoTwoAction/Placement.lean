module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.JankoTwoAction.Models
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.JankoTwoAction.Placement.Source
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.JankoTwoAction.Placement.FixedModel

/-!
# A compatible local marking in the actual automorphism group of J₂

The source product Y₊S maps to a subgroup containing a full Sylow two-subgroup,
with order prime to five and divisible by nine. The checked J₂ overgroup
placement and the outer automorphism action identify its conjugate with the
full normalizer of the fixed second radical. The two-residual identity then
identifies Y₊ under the very same conjugation.

Only the earlier component setup and its compatible J₂ identification are
inputs. No four-space action, moved-space order, or centralizer calculation
is needed for this marking.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), final paragraph
of 15.3.42, printed p.1138; GLS3 Table 5.3g. The finite model certificates and
their ATLAS attribution are retained in the imported placement modules.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.JankoTwoAction

variable {G : Type*} [Group G] [Finite G]
variable {I L M Yplus S : Subgroup G} [(L.subgroupOf I).Normal]

/-- One conjugator identifies both the source local group and its two-residual. -/
theorem nonempty_localMarking (d : ComponentSetup I L M Yplus S)
    (j : JankoTwoIdentification I L) : Nonempty (LocalMarking j Yplus S) := by
  obtain ⟨P, hP⟩ := modelImage_sylow d j
  obtain ⟨g, hg⟩ := Placement.exists_conjugate_eq_secondNormalizer
    (modelImage j (Yplus ⊔ S))
    ⟨P, by rw [hP]; exact map_mono (subgroupOf_mono I le_sup_right)⟩
    (modelImage_join_five_free d j) (modelImage_join_nine_dvd d j)
  exact ⟨localMarkingOfJoinConjugacy d j g hg⟩

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.JankoTwoAction
