module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.TripleSevenExclusion.Reduction

/-!
# The genuine triple-seven exclusion in K.1

The proved elementary conjugate-generation budget in A₇ closes the intrinsic
binary representation argument: cubic ratio at most two forces degree at most
eight, whereas a faithful irreducible module for the genuine triple cover has
degree at least twelve. The outer restriction theorem transports the small
cubic actor into the component, giving the exclusion for the full ambient
Chapter K input as well.

The final Recognition application discharges the triple-seven branch. Only
the separate A₆, A₇ and triple-six recognition inputs remain explicit; neither
a generation bound nor a triple-seven representation premise is assumed.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, K.1, printed p.452/PDF p.463. This proves the
triple-seven exclusion used there in the appeal to Guralnick–Malle (2002),
Theorem 6.2 and Table 6.3.
-/

public section

namespace CFSG.Quasithin.ChapterK.Alternating

universe u v

/-- Recognition with the triple-seven branch discharged by its source proof.
The other three representation branches retain their independent inputs. -/
theorem recognition_of_six_seven_tripleSix
    (h6 : RecognitionInputs.SixRecognition.{u,v})
    (h7 : RecognitionInputs.SevenRecognition.{u,v})
    (h36 : RecognitionInputs.TripleSixDegree.{u,v})
    {G : Type u} {V : Type v} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) {K : GroupClass.{u}}
    {L : Subgroup G} (h : Input ρ K L) : RecognizedAction ρ L :=
  recognition_of_branches h6 h7 h36 tripleSevenExclusion ρ h

end CFSG.Quasithin.ChapterK.Alternating
