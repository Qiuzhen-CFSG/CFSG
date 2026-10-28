module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.CoreRecognition
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.CoreRecognition.SylowInputs.CubicPlane
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.CoreRecognition.SylowInputs.TwoPart
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.CoreRecognition.SylowInputs.ThreePlacement

/-!
# Assembly of the independent Sylow inputs for 47.3

The second-centralizer alternatives give nonabelian ambient Sylow threes
before recognition of the first centralizer. `CubicPlane` constructs the
literal elementary group X × Y of order nine, with z fixing X and
inverting Y, and proves that C_G(Y) has three-part nine.

`TwoPart` computes the actual core fixed subgroup C_Q(X) of order eight
and uses both involution-centralizer models to bound every two-subgroup
of C_G(X). `ThreePlacement` uses conjugation on the four lines of X × Y
to place an ambient Sylow three in C_G(X), without assuming that z
normalizes a Sylow extension of the plane. Together these prove
`core_sylow_data` from the earlier conclusions and the explicit
second-centralizer alternatives.

The final consumer discharges the entire `CoreSylowData` premise of the
independent A₆-cover recognition theorem. Its cover conclusions play no
part in constructing the Sylow inputs. The alternatives remain with
`qt-i47-j2-second-centralizer-alternative`; their final discharge and the
independent normalizer index remain with
`qt-i47-j2-three-centralizer-core-recognition`.

Source: Aschbacher, *Sporadic Groups* (1994), 47.3, printed p.262.
-/

@[expose] public section

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal
namespace EarlierConclusions

variable {G : Type*} [Group G] [Finite G] {D : Seed G}

/-- The two remaining local inputs, with nonabelianity discharged by the source alternatives. -/
theorem core_sylow_data_of_two_card_and_three_placement (E : EarlierConclusions D)
    (hAlt : SecondNormalizer.CentralizerAlternatives E.geometry)
    (hTwo : ∀ T : Sylow 2 (C D), Nat.card T = 8)
    (hThree : ∃ P : Sylow 3 G, (P : Subgroup G) ≤ C D) : CoreSylowData D := by
  obtain ⟨P, hP⟩ := hThree
  exact ⟨hTwo, P, hP, CoreSylowInputs.three_noncommutative E hAlt P⟩

/-- Application to the literal cover-recognition consumer; the local bounds and index remain explicit. -/
theorem core_recognition_of_two_card_and_three_placement (E : EarlierConclusions D)
    (hAlt : SecondNormalizer.CentralizerAlternatives E.geometry)
    (hTwo : ∀ T : Sylow 2 (C D), Nat.card T = 8)
    (hThree : ∃ P : Sylow 3 G, (P : Subgroup G) ≤ C D)
    (hi : (CM D).index = 2) :
    Theory.GroupTheory.IsQuasisimple (C D) ∧
    Nonempty ((C D ⧸ XC D) ≃* alternatingGroup (Fin 6)) ∧
    (InvolutionGeometry.rootComponent E.geometry.t ⊔ D.X).relIndex (C D) = 6 :=
  E.core_recognition_of_sylow_data
    (E.core_sylow_data_of_two_card_and_three_placement hAlt hTwo hThree) hi

/-- The independent Sylow inputs of 47.3, with both local calculations discharged.
Only the separately constructed second-centralizer alternatives remain explicit. -/
theorem core_sylow_data [IsSimpleGroup G] (E : EarlierConclusions D)
    (hAlt : SecondNormalizer.CentralizerAlternatives E.geometry) : CoreSylowData D :=
  E.core_sylow_data_of_two_card_and_three_placement hAlt
    (CoreSylowInputs.two_card E) (CoreSylowInputs.exists_three_in_centralizer E hAlt)

/-- Application to the actual A₆-cover recognition: the alternatives and the
independent normalizer index are the only premises beyond the earlier source data. -/
theorem core_recognition_of_centralizer_alternatives [IsSimpleGroup G]
    (E : EarlierConclusions D)
    (hAlt : SecondNormalizer.CentralizerAlternatives E.geometry)
    (hi : (CM D).index = 2) :
    Theory.GroupTheory.IsQuasisimple (C D) ∧
    Nonempty ((C D ⧸ XC D) ≃* alternatingGroup (Fin 6)) ∧
    (InvolutionGeometry.rootComponent E.geometry.t ⊔ D.X).relIndex (C D) = 6 :=
  E.core_recognition_of_sylow_data (E.core_sylow_data hAlt) hi

end EarlierConclusions
end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal
