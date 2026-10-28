module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankThree.SmallDegree
public import Theory.Representation.PSL3Three.NativeFieldCalculation.Models

/-!
# Native Frobenius descent for the PSL₃(3) source action

The native constructions and proved conjugacy-class bound supply both the small
absolute-degree window and the degree-sixteen field obstruction. Applying them
to the existing faithful action on the generalized Fitting subgroup yields the
same source degree-twelve conclusion. The final theorem discharges both native
construction premises. The independent central-cover premise remains explicit;
this module does not assert that separate group-theoretic calculation.

Source: Guralnick--Malle, *Classification of 2F-modules I*, Proposition 4.2;
Aschbacher--Smith K.2, printed p.453.
-/

public section
open Subgroup Theory.GroupTheory Representation

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankThree
universe u v
variable {G : Type u} {V : Type v} [Group G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (h : SourceAction ρ)

include h

/-- Native module constructions and the proved odd-class bound discharge both
representation-theoretic premises of the existing source consumer. -/
theorem source_degree_twelve_of_centerless_and_native_inputs
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 3 3)
    (hrank : primeRank 2 G ≤ 3)
    (hdim : 12 ≤ Module.finrank (ZMod 2) V)
    (hbound : Module.finrank (ZMod 2) V ≤ 6 * primeRank 2 G)
    (hcenter : center (generalizedFitting G) = ⊥)
    (hprincipal : Representation.PSL3Three.AbsoluteDegrees.PrincipalModelsExist.{v})
    (hsixteen : Representation.PSL3Three.AbsoluteDegrees.SixteenModelsExist.{v}) :
    Module.finrank (ZMod 2) V = 12 :=
  source_degree_twelve_of_centerless_and_absolute_calculations ρ h hm hrank hdim hbound
    hcenter
    (Representation.PSL3Three.AbsoluteDegrees.absoluteDegreeWindow_of_constructions
      hprincipal hsixteen Matrix.PSL3Three.odd_conjClasses_card_le_seven)
    (Representation.PSL3Three.NativeFieldCalculation.degreeSixteenFieldObstruction_of_models
      hprincipal hsixteen)

/-- The native representation calculation on the actual source action, with
no character, field, class-count or model-construction premise. The centerless
cover is the independent group-theoretic assumption retained from the consumer. -/
theorem source_degree_twelve_of_centerless_native_calculation
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 3 3)
    (hrank : primeRank 2 G ≤ 3)
    (hdim : 12 ≤ Module.finrank (ZMod 2) V)
    (hbound : Module.finrank (ZMod 2) V ≤ 6 * primeRank 2 G)
    (hcenter : center (generalizedFitting G) = ⊥) :
    Module.finrank (ZMod 2) V = 12 :=
  source_degree_twelve_of_centerless_and_native_inputs ρ h hm hrank hdim hbound hcenter
    Representation.PSL3Three.AbsoluteDegrees.principalModelsExist
    Representation.PSL3Three.AbsoluteDegrees.SixteenModels.sixteenModelsExist

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankThree
