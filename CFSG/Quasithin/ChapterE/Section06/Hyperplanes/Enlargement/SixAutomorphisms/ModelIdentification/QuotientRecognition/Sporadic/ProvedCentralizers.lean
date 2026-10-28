module
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.Sporadic.Held
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Outer
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassB.Closure.Application
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoFour
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.J2Inner
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.J2Outer
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.OuterInvolutionCentralizer.PermutationComparison
/-!
# Proved involution-centralizer exclusions for three sporadic models

The Held fixed rows and the Janko-four component theorem exclude an A₆
component. For J₂ the inner component is A₅, while every outer involution
has fixed subgroup of order 336. The latter argument needs only the proved
cardinality, so no identification of the outer small model is assumed.

The source applications retain the literal quotient Y/Z(Y), with simplicity
and perfectness inherited from the original normal component.

Source: Aschbacher–Smith, E.6.23, printed p.254 (PDF p.265), and 16.1.5,
printed p.1172.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.Sporadic

/-- The complete Held inner and outer fixed rows exclude an A₆ component. -/
theorem held : FixedSixExclusion Held.He :=
  held_of_involution_rows Held.Realization.normalizer_surjective
    Held.InvolutionFixedData.innerRows Held.InvolutionFixedData.outerRow

/-- Every J₄ involution fixed subgroup has no components. -/
theorem janko_four [IsSimpleGroup Janko4.Model] [Group.IsPerfect Janko4.Model] :
    FixedSixExclusion Janko4.Model := by
  intro a ha K hK
  exact (Chapter16.OtherPreliminaries.JankoFour.involution_fixed_no_component a ha K hK).elim
/-- Both inner classes and the outer class of the concrete J₂ carrier. -/
theorem janko_two : FixedSixExclusion _root_.Sporadic.LeechRelated.J2.Carrier := by
  intro a ha K hK he
  by_cases hi : ∃ g, a = MulAut.conj g
  · obtain ⟨e⟩ := Chapter16.OtherPreliminaries.JankoTwoHigmanSims.J2Inner.inner_component_equiv
      a ha hi K hK
    obtain ⟨f⟩ := he
    have hc := Nat.card_congr (e.symm.trans f).toEquiv
    change Nat.card (alternatingGroup (Fin 5)) = Nat.card (alternatingGroup (Fin 6)) at hc
    rw [nat_card_alternatingGroup, nat_card_alternatingGroup] at hc
    norm_num at hc
  · obtain ⟨e⟩ := Chapter16.OtherPreliminaries.JankoTwoHigmanSims.J2Outer.outer_fixed_representative
      a ha hi
    obtain ⟨f⟩ := he
    have hd := K.card_subgroup_dvd_card
    rw [Nat.card_congr e.toEquiv,
      _root_.Sporadic.LeechRelated.J2.OuterInvolutionCentralizer.card_fixed,
      Nat.card_congr f.toEquiv, nat_card_alternatingGroup] at hd
    norm_num at hd

variable {G : Type*} [Group G] [Finite G]

/-- The actual Held quotient is excluded in the further enlargement. -/
theorem held_source (T : Sylow 2 G) (M V : Subgroup G) [IsElementaryAbelian 2 V] :
    SourceExclusion Held.He T M V :=
  sourceExclusion_of_fixed_exclusion (fun _ _ => held) T M V

/-- The J₄ carrier inherits its required instances from the original quotient. -/
theorem janko_four_source (T : Sylow 2 G) (M V : Subgroup G) [IsElementaryAbelian 2 V] :
    SourceExclusion Janko4.Model T M V :=
  sourceExclusion_of_fixed_exclusion (fun _ _ => janko_four) T M V

/-- The actual J₂ quotient is excluded without an outer model-comparison premise. -/
theorem janko_two_source (T : Sylow 2 G) (M V : Subgroup G) [IsElementaryAbelian 2 V] :
    SourceExclusion _root_.Sporadic.LeechRelated.J2.Carrier T M V :=
  sourceExclusion_of_fixed_exclusion (fun _ _ => janko_two) T M V

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.Sporadic
