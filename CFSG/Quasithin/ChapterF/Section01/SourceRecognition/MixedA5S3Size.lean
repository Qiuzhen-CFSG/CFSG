module

public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.MixedA5S3Size.LocalStructure
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.MixedA5S3Size.ReducedBorel
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.MixedA5S3Size.OuterTransport

/-!
# Mixed F.1.12 size assembly from structural recognition

The concrete Borel orders and the original F.1.1 Sylow witness give the
bound required in original 9.3.1. The only outstanding premise is the
structural recognition of the mixed pair. This conditional theorem does
not assert that F.1.12 has been proved.

Source: Aschbacher--Smith, F.1.12(I), printed pp.262--264, and original
9.3.1, printed p.732 of refs/quasithin.pdf.
-/

public section
namespace CFSG.Quasithin.ChapterF.Source
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The exact source hypotheses imply the size bound once Borel recognition
is supplied. No global identification or compatible amalgam marking is needed. -/
theorem mixed_a5_s3_sylow_card_le_of_borel_recognition
    (recognition : MixedA5S3BorelRecognition G)
    (K U S : Subgroup G) (h : HypothesisF11 ![K,U] S)
    (hqt : IsQuasithin (generated ![K,U] S))
    (hSyl : Chapter1.IsSylowIn 2 S (generated ![K,U] S))
    (hK : Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)))
    (hU : Nonempty ((U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3))) :
    Nat.card S ≤ 256 := by
  exact h.sylow_card_le_of_mixedBorelModel
    (recognition K U S h hqt hSyl hK hU (h.cubic_borel_normalizes_S 1 hU.some))

end CFSG.Quasithin.ChapterF.Source
