module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FaithfulAction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.OffenderActor
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.Models
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.Line
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.MarkedActors
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization.Generated
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization.ModelCases
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization.Orthogonal
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization.Reduction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization.Sieve

/-!
# The marked degree-eight FF specialization

The actual offender actor satisfies the input conditions of B.5.1, and its
component commutator module is the whole original U_L. The actual alternating
group equivalence comes from the original star marking, not from an equality
of orders. The SQTK input remains explicit on the original component.

The orthogonal quotient transports back from the offender actor and its
coordinates are reconciled with the original star marking using Aut(A₈).
ModelCases retains the repeated-natural branch of B.5.1. Marking transports
the actual middle parabolic between independently chosen projective coordinates.
Reduction then excludes both natural branches using the actual moving line,
including every multiplicity in the repeated-natural case. The classification
sieve handles all four branches of B.5.1(1), using B.4.2 and I.1.6 to remove
the other models and split the four-dimensional natural central cover.

`alternatives_of_source` applies that sieve to J and constructs the published
Models.Alternatives for the original component action and parabolic marking.
Its only classification inputs are the independent universal statements in
Sieve.Source; its SQTK hypothesis uses the complete known-simple class on the
actual component. This completes the conditional specialization, not the
universal earlier theorems or the later removal of the orthogonal-cover kernel.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1 and
15.3.32(1), printed pp.99–103 and 1132–1133.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization
universe u
variable {G : Type u} [Group G] [Finite G]
  (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
  (hn : (c.L.subgroupOf I).Normal) (hI : I = c.L ⊔ d.S)
  (hchar : HasCharacteristicTwo I)
  (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
  [IsElementaryAbelian 2 ((d.componentModule I c.L).subgroupOf I)]
  (e : d.Star I ≃* Equiv.Perm (Fin 8))
  (he : (d.starImage I c.L).map e.toMonoidHom = alternatingGroup (Fin 8))

include e he in
/-- All source input conditions hold at J, retaining the genuine SQTK premise
on the original component and proving the full commutator condition. -/
theorem offenderInput {known : GroupClass}
    (hSQTK : IsSQTK known (d.starImage I c.L)) (hYL : d.Yplus ≤ c.L) :
    FFInput known (offenderAction d c hn hI hchar P hP)
      (offenderComponent d c hn hI hchar P hP) where
  normal := offenderComponent_normal d c hn hI hchar P hP
  quasisimple := offenderComponent_quasisimple d c hn hI hchar P hP e he
  sqtk := offenderComponent_sqtk d c hn hI hchar P hP e he hSQTK
  faithful := offenderAction_faithful d c hn hI hchar P hP
  twoCore := offenderGroup_twoCore d c hn hI hchar P hP
  offenders := offenderAction_generated d c hn hI hchar P hP
  generalizedFitting := offenderGroup_generalizedFitting_eq_component_sup_center
    d c hn hI hchar P hP e he
  full := offenderAction_full d c hn hI hchar P hP hYL e he

/-- The component of J is the alternating group via the original S₈ marking. -/
noncomputable def offenderComponent_alternating :
    offenderComponent d c hn hI hchar P hP ≃* alternatingGroup (Fin 8) :=
  (subgroupOfEquivOfLe (component_le_offenderGroup d c hn hI hchar P hP e he)).trans
    ((e.subgroupMap (d.starImage I c.L)).trans (MulEquiv.subgroupCongr he))

/-- An orthogonal quotient classified on J gives the published cover for the
original star action and original marking; its kernel remains C_{U_L}(L). -/
noncomputable def offenderOrthogonalCover (hYL : d.Yplus ≤ c.L)
    (h : OrthogonalQuotient (offenderAction d c hn hI hchar P hP)
      (offenderComponent d c hn hI hchar P hP)) :
    Models.OrthogonalCover (componentAction d c hn hI hchar P hP)
      (d.starImage I c.L) e :=
  (h.of_subgroupOf (component_le_offenderGroup d c hn hI hchar P hP e he)).markedCover
    e he (componentAction_full d c hn hI hchar P hP hYL)

include he in
/-- Final geometric assembly on the original component action, conditional only
on the still-required unmarked classification output for the offender actor.
The source specialization must derive `hcases` from universal earlier theorems;
this conditional reduction is not itself the B.5.1 specialization. -/
theorem alternatives_of_offender_cases (hYL : d.Yplus ≤ c.L)
    (hline : LineData d I)
    (mark : Models.MiddleNodeMarking (d.starImage I c.L) (d.starImage I (d.M ⊓ c.L)))
    (hcases : UnmarkedCases (offenderAction d c hn hI hchar P hP)
      (offenderComponent d c hn hI hchar P hP)) :
    Models.Alternatives (componentAction d c hn hI hchar P hP)
      (d.starImage I c.L) (d.starImage I (d.M ⊓ c.L)) e mark := by
  have hcases' : UnmarkedCases (componentAction d c hn hI hchar P hP)
      (d.starImage I c.L) :=
    hcases.of_subgroupOf (component_le_offenderGroup d c hn hI hchar P hP e he)
  exact Or.inl (orthogonalCover_of_unmarked hcases' e he
    (componentAction_full d c hn hI hchar P hP hYL) mark
    (hline.movingLine d c hn hI hchar P hP hYL)
    (hline.yplus_star_le_parabolic d c hYL))

include he in
/-- The universal B.5.1/B.4.2 classification and I.1.6 cohomology calculation
give the two published alternatives on the actual component module. All local
FF premises are proved at the offender group J, and the original star and
middle-parabolic markings are retained. The orthogonal-cover kernel remains
exactly the component-fixed space; its vanishing is a later obligation. -/
theorem alternatives_of_source
    (classification : Sieve.UniversalFFClassification.{u,u})
    (cohomology : Sieve.UniversalNaturalCohomology)
    (hSQTK : IsSQTK KnownSimple.IsKnownSimple (d.starImage I c.L))
    (hYL : d.Yplus ≤ c.L) (hline : LineData d I)
    (mark : Models.MiddleNodeMarking (d.starImage I c.L) (d.starImage I (d.M ⊓ c.L))) :
    Models.Alternatives (componentAction d c hn hI hchar P hP)
      (d.starImage I c.L) (d.starImage I (d.M ⊓ c.L)) e mark := by
  apply alternatives_of_offender_cases d c hn hI hchar P hP e he hYL hline mark
  exact Sieve.unmarkedCases classification cohomology
    (offenderInput d c hn hI hchar P hP e he hSQTK hYL)
    (offenderComponent_alternating d c hn hI hchar P hP e he)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization

end
