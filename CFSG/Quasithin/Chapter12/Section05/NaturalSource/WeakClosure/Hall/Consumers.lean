module

public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Zero.Consumers

/-!
# The exterior Hall conclusion from the preceding local geometry

Apply the proved generation-one exclusion to the original H-star member,
then apply the specialized 12.2.11(a) Hall argument. This supplies the
generation-two and nontrivial Hall-three conclusions used in the final
paragraph of 12.5.1, on the unchanged H, M and exterior module.

Structural1222At is produced by qt-d-1222-source and discharged by
qt-d-1251-source. The G₃,G₆ and point-core containments retain their producer
qt-d-1251-local; the terminal configuration and final classification assembly
remain with qt-d-1251-fusion. No action, normalizer, numerical generation or
Hall-subgroup premise remains in this application.

Source: Aschbacher--Smith, 12.5.11(1), 12.5.12 and the proof of 12.5.1,
printed pp.821--822.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02 ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}

/-- The literal 12.5.12 consumer with the preceding generation-one
exclusion discharged by the original weak-closure and point geometry. -/
theorem exterior_generation_two_and_hall_three_of_source_parameters
    (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hG₃ : s.marking.Gi 3 ≤ s.marking.M)
    (hG₆ : s.marking.Gi 6 ≤ s.marking.M)
    (hcore : V ≤ (s.marking.Gi 1).pCoreIn 2)
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M)
    (hHGi : H ≤ s.marking.Gi 1) :
    generationParameter H = 2 ∧
      ∃ C : Subgroup G, C ≠ ⊥ ∧ C ≤ H ⊓ s.marking.M ∧
        IsHallSubgroup oddPrimes (C.subgroupOf (H ⊓ s.marking.M)) ∧
        IsPGroup 3 C :=
  exterior_generation_two_and_hall_three D h s hH hHGi
    (generation_ne_one_of_source_parameters s h structural hG₃ hG₆ hcore hH) structural

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
