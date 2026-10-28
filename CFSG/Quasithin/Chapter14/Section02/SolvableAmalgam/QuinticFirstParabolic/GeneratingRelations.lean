module

public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.Source
public import Theory.SpecificGroups.Tits.FirstParabolicCoordinates
public import Theory.SpecificGroups.ReeTwo.GeneratingRecognition
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic.SylowCoordinates
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic.WeylActor
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic.LowerBound

/-!
# The generation step for the original quintic first parabolic

The coordinate constructors must supply eight actual generators of the
original Sylow group, their twenty-one Sylow equations, and an outside
involution satisfying the seven remaining local equations. Index five then
proves generation of the original H and supplies the exact relation data
consumed by whole-parabolic recognition.

The intrinsic-centralizer consumer constructs the coordinates and actor,
and discharges the numerical premise using the proved original Sylow bound.
The intrinsic centralizer itself remains to be constructed under the source
hypotheses by qt-e-quintic-first-parabolic.

Source: Aschbacher--Smith14.2.20--21, printed pp.988--989, and Parrott (1972),
§5, p.683. See `refs/original/n-group-global/parrott-tits-presentation.md`.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic
variable {G : Type*} [Group G]

/-- Apply the generation argument to the literal original H and Sylow T.
Only Sylow generation is an input; generation of H is proved using index five.
The original source construction must still supply both coordinate inputs. -/
theorem source_generating_relations_of_coordinates
    (T : Sylow 2 G) {M : Subgroup G} (H : Subgroup G)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (d : Tits.FirstParabolicCoordinates.SylowCoordinates
      (T.subtype hH.1.1.2 : Subgroup H))
    (r : Tits.FirstParabolicCoordinates.WeylExtension d) :
    Nonempty (ReeTwo.Centralizer.Generators H) ∨
      Nonempty (Tits.FirstParabolicPresentation.Generators H) := by
  exact Or.inr ⟨Tits.FirstParabolicCoordinates.generators d r hi⟩

open Stellmacher Theory.GroupTheory
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

/-- The intrinsic centralizer input produces the complete original generating
tuple. The original Sylow lower bound supplies the actor's numerical premise;
no coordinates, actor, presentation equations or generation are assumed. -/
theorem source_generating_relations_of_intrinsic [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hintrinsic : ∃ z : G, zpowers z = centralInvolutions T ∧
      Recognition.ParrottCentralizerHypotheses z) :
    Nonempty (ReeTwo.Centralizer.Generators H) ∨
      Nonempty (Tits.FirstParabolicPresentation.Generators H) := by
  obtain ⟨d⟩ := source_sylow_coordinates_of_intrinsic hG T hempty H hH hintrinsic
  obtain ⟨d',⟨r⟩⟩ := source_weyl_actor_of_intrinsic
    hG T hempty hM hu hmany hcard e H hH hi
    (source_quintic_sylow_lower hG T hempty hM hu hmany hcard e H hH hi) d hintrinsic
  exact source_generating_relations_of_coordinates T H hH hi d' r

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic
