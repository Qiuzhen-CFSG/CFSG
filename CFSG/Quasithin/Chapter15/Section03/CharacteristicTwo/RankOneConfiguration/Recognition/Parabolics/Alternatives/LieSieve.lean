module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Alternatives.LieSieve.LinearTwo
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Alternatives.LieSieve.LinearThree
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Alternatives.LieSieve.Symplectic
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Alternatives.LieSieve.G2
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Alternatives.LieSieve.BinaryHigher
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Alternatives.LieSieve.G2Recognition.Source
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Exceptional

/-!
# The exhaustive marked Lie-model inspection in 15.3.28

The center calculation excludes the genuine triple cover of A₆ and forces
the degree of an SL₃ field to be odd. Together with the separately supplied
A₇ exclusion, this reduces the complete FF list to eight concrete cases.
The model inspections then construct an even-degree linear-two Borel,
a labeled binary rank-two parabolic, or the outer middle-node SL₄(2)
configuration. The A₆ branch uses an actual equivalence with Sp₄(2)′;
the full symplectic and G₂ models and SL₅(2) are excluded.

The local geometry leaf proves the Sylow, maximality, residual and order
constraints used in each inspection. The surviving markings identify the
literal component intersection under actual model equivalences. Both
labeled parabolic classes are preserved in the small alternatives; the
middle-node alternative includes self-centralization and outer Sylow
action. The final theorem assumes only the earlier local inputs, the
complete FF model list and the separately proved A₇ exclusion. Its parent
constructs those two inputs and converts the outer middle-node data into
the eight-point permutation marking. No later 15.3.30–31 exclusion is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.5–6,
printed pp.104–105, and 15.3.27–28, printed pp.1130–1131.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.LieSieve

/-- The unreconciled concrete models after the center and A₇ exclusions.
No parabolic statement or small-field restriction is encoded in this list. -/
inductive RemainingModel (H : Type*) [Group H] : Prop
  | linearTwo (F : ClassificationField)
      (equiv : H ≃* Matrix.SpecialLinearGroup (Fin 2) F.Carrier)
  | linearThree (F : ClassificationField) (odd : Odd F.degree)
      (equiv : H ≃* Matrix.SpecialLinearGroup (Fin 3) F.Carrier)
  | symplecticFour (F : ClassificationField)
      (equiv : H ≃* Matrix.symplecticGroup (Fin 2) F.Carrier)
  | g2 (F : ClassificationField) (equiv : H ≃* Atlas.G2.Model F.Carrier)
  | alternatingSix (equiv : H ≃* alternatingGroup (Fin 6))
  | g2DerivedTwo (equiv : H ≃* commutator (Atlas.G2.Model (ZMod 2)))
  | linearFourTwo (equiv : H ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))
  | linearFiveTwo (equiv : H ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))

variable {G : Type*} [Group G] [Finite G]
variable {d : LocalData G} {I : Subgroup G} {c : ComponentWitness d I}

/-- Inspect the complete earlier list for the two center obstructions and
the supplied A₇ exclusion. The remaining parabolic constructions are separate. -/
theorem remaining_models (a : Input d I c)
    (hmodel : FFComponentModel (d.starImage I c.L))
    (hA7 : ¬ Nonempty (d.starImage I c.L ≃* alternatingGroup (Fin 7))) :
    RemainingModel (d.starImage I c.L) := by
  cases hmodel with
  | linearTwo F e => exact .linearTwo F e
  | linearThree F e =>
    refine .linearThree F (Nat.not_even_iff_odd.mp ?_) e
    intro heven
    exact not_even_specialLinearThree d a.minimal.1 c a.facts a.solvableControl
      a.normal F.Carrier F.degree heven F.card_eq ⟨e⟩
  | symplecticFour F e => exact .symplecticFour F e
  | g2 F e => exact .g2 F e
  | alternatingSix e => exact .alternatingSix e
  | alternatingSeven e => exact (hA7 ⟨e⟩).elim
  | tripleSix z q =>
    apply False.elim
    apply not_tripleCoverAlternatingSix d a.minimal.1 c a.facts a.solvableControl a.normal
    refine ⟨c.star_quasisimple, ?_, ⟨q⟩⟩
    exact (Nat.card_congr z.toEquiv).trans (by simp)
  | g2DerivedTwo e => exact .g2DerivedTwo e
  | linearFourTwo e => exact .linearFourTwo e
  | linearFiveTwo e => exact .linearFiveTwo e

/-- Inspect every remaining concrete model, constructing the literal Borel
or parabolic marking and all action fields in each surviving branch. -/
theorem lieParabolicAlternative_of_remaining_model (a : Input d I c)
    (hmodel : RemainingModel (d.starImage I c.L)) :
    LieParabolicAlternative d I c := by
  cases hmodel with
  | linearTwo F e =>
    obtain ⟨marking⟩ := linearTwo_marking a F e
    exact .linearTwo F marking
  | linearThree F hodd e =>
    obtain ⟨marking⟩ := linearThree_marking a F hodd e
    exact .small (.linearThree marking)
  | symplecticFour F e => exact (symplecticFour_excluded a F e).elim
  | g2 F e => exact (g2_excluded a F e).elim
  | alternatingSix e =>
    obtain ⟨marking⟩ := alternatingSix_marking a e
    exact .small (.symplecticDerived marking)
  | g2DerivedTwo e =>
    obtain ⟨marking⟩ := g2DerivedTwo_marking a e
    exact .small (.g2Derived marking)
  | linearFourTwo e =>
    obtain ⟨marking⟩ := BinaryHigher.four_branch a e
    exact .middle marking
  | linearFiveTwo e => exact (BinaryHigher.five_branch a e).elim

/-- The exhaustive Lie-geometric sieve in the second paragraph of 15.3.28.
The full FF model list and A₇ exclusion are the two explicit inputs supplied
by the parent; no parabolic position, field restriction or diagram action
is assumed. -/
theorem lieParabolicAlternative (a : Input d I c)
    (hmodel : FFComponentModel (d.starImage I c.L))
    (hA7 : ¬ Nonempty (d.starImage I c.L ≃* alternatingGroup (Fin 7))) :
    LieParabolicAlternative d I c :=
  lieParabolicAlternative_of_remaining_model a (remaining_models a hmodel hA7)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.LieSieve
