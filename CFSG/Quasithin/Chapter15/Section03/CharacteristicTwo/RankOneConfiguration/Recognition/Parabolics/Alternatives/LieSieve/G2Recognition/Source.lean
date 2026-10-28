module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Alternatives.LieSieve.G2Recognition
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Alternatives.LieSieve.G2TwoCore

/-!
# Recognition of the G₂ component intersection from the source inputs

For the literal intersection J = (M ∩ L)* inside L*, the S₃ shadow,
prime-to-three residual and three-subgroup order bound give O₂(J) ≠ 1.
The G₂ normalizer cover then puts J in a root parabolic. Aligning the
component Sylow makes both root parabolics S*-invariant, and source
maximality promotes containment to equality.

The two-core premise of the conditional recognition API is discharged here
for both actual carriers. The full model yields a full root parabolic;
the binary derived model yields a marking with both diagram labels fixed.
These are the G₂ recognition steps in the inspection, not the remaining
exclusion of the full models or the complete alternatives of 15.3.28.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.26–28,
printed pp.1130–1131 (PDF pp.1147–1148).
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.LieSieve.G2Recognition
open Atlas.G2 Atlas.G2.LieParabolicSetup
variable {G : Type*} [Group G] [Finite G]
variable {d : LocalData G} {I : Subgroup G} {c : ComponentWitness d I}

/-- The source intersection in a full G₂ model is a standard root parabolic
under a suitable marking of that same full carrier. -/
theorem full_recognition (a : Input d I c) (F : ClassificationField)
    (e : d.starImage I c.L ≃* Model F.Carrier) :
    ∃ (f : d.starImage I c.L ≃* Model F.Carrier) (i : Fin 2),
      ((d.starImage I (d.M ⊓ c.L)).subgroupOf (d.starImage I c.L)).map f.toMonoidHom =
        (if i = 0 then parabolic₁ else parabolic₂) :=
  full_recognition_of_twoCore a F e (G2TwoCore.full_twoCore_ne_bot a F e)

/-- The G₂(2)′ intersection is a standard derived parabolic, with trivial
S-action on both diagram labels, from the source input alone. -/
theorem binary_marking (a : Input d I c)
    (e : d.starImage I c.L ≃* commutator (Model (ZMod 2))) :
    Nonempty (RankTwoParabolicMarking d I c.L (commutator (Model (ZMod 2)))
      g2DerivedParabolic) :=
  binary_marking_of_twoCore a e (G2TwoCore.binary_twoCore_ne_bot a e)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.LieSieve.G2Recognition
