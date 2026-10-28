module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.ProductGeometry.Supplements
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.ProductGeometry.ModelFacts
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.ProductGeometry.Localization
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.ProductGeometry.SymmetricFive

/-!
# B.5.10 from the five component actions of B.5.9

For each of the four B.5.9 alternatives with first factor L, the actual model
proves faithfulness, trivial center and the fixed-supplement or exceptional
hyperplane alternative. These applications pass those results to the existing
offender-image product construction, which supplies the multiplication
equivalence and the equality C_G(L) = C_G(W).

The intermediate branch applications retain their existing interfaces. The
final case split discharges their offender-localization premises on the literal
ambient action image. In the marked S5 case, the actual A5 normalizer supplies
normality of LA and coverage of the image, and cohomology supplies the direct
sum with C_V(L). Thus all three clauses of B.5.10 follow from the actual B.5.9
alternative, without further model or earlier-source premises. In particular
the nonsplit natural SL3(2) quotient has dimension exactly one; the distinct
four-dimensional moved cover always has a fixed supplement.

The final consumer packages the constructed product with the supplied B.5.9
action in `ComponentReduction.Conclusion`. Construction of that preceding
action alternative remains the parent component-reduction task's obligation.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.9–10,
printed pp.107–109.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.ProductGeometry
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {K : GroupClass.{u}}

/-- The SL2 application discharges faithfulness, centerlessness and the
Gaschütz supplement by proved matrix and odd-coset calculations. -/
theorem configuration_linearTwo (hyp : FFHypothesis K ρ)
    {A L : Subgroup G} [L.Normal] (s : MovedSection ρ L) (F : BinaryField)
    (hn : IsLinearNatural (s.action.comp L.subtype) F 2)
    (hsyl : ∃ T : Sylow 2 L, A = (T : Subgroup L).map L.subtype)
    (hs : s.space.toSubmodule ⊔ fixedSpace ρ A = ⊤)
    (hloc : ∀ D, IsBestOffender (subspaceImageRepresentation ρ s.space.toSubmodule) D →
      D ≤ restrictedSubgroup ρ s.space.toSubmodule L) :
    Nonempty (ProductConfiguration ρ L s.space) := by
  let := hyp.finite_module
  obtain ⟨hf, hz⟩ := linearTwo_faithful_center s F hn
  exact configuration_of_offender_image ρ hyp.generated s.space L hf hz hloc
    (Or.inl (sylow_supplement s hsyl hs))

/-- The doubled SL3 application uses the actual contained offender, including
the binary endpoint of the source extension argument. -/
theorem configuration_doubleThree (hyp : FFHypothesis K ρ)
    {A L : Subgroup G} [L.Normal] (s : MovedSection ρ L) (F : BinaryField)
    (ho : Odd F.degree) (hA : IsBestOffender ρ A) (hAL : A ≤ L)
    (hn : IsRepeatedLinearNatural (s.space.toRepresentation.comp L.subtype) F 3 2)
    (hloc : ∀ D, IsBestOffender (subspaceImageRepresentation ρ s.space.toSubmodule) D →
      D ≤ restrictedSubgroup ρ s.space.toSubmodule L) :
    Nonempty (ProductConfiguration ρ L s.space) := by
  let := hyp.finite_module
  obtain ⟨hf, hz⟩ := doubleThree_faithful_center s F ho hn
  exact configuration_of_offender_image ρ hyp.generated s.space L hf hz hloc
    (Or.inl (doubleThree_supplement s F hA hAL hn))

/-- The natural SL3 application derives the literal exceptional quotient of
dimension one from the computed first cohomology. -/
theorem configuration_naturalThree (hyp : FFHypothesis K ρ)
    {L : Subgroup G} [L.Normal] (s : MovedSection ρ L) (F : BinaryField)
    (ho : Odd F.degree)
    (hn : IsLinearNatural (s.space.toRepresentation.comp L.subtype) F 3)
    (hloc : ∀ D, IsBestOffender (subspaceImageRepresentation ρ s.space.toSubmodule) D →
      D ≤ restrictedSubgroup ρ s.space.toSubmodule L) :
    Nonempty (ProductConfiguration ρ L s.space) := by
  let := hyp.finite_module
  obtain ⟨hf, hz⟩ := naturalThree_faithful_center s F ho hn
  exact configuration_of_offender_image ρ hyp.generated s.space L hf hz hloc
    (naturalThree_supplement_or_exceptional s F hn)

/-- The four-dimensional moved cover has a fixed supplement. Its natural
central quotient is not confused with B.4.8(3)'s upper extension. -/
theorem configuration_fourCover (hyp : FFHypothesis K ρ)
    {A L : Subgroup G} [L.Normal] (s : MovedSection ρ L)
    (hA : IsBestOffender ρ A) (hAL : A ≤ L)
    (cover : FourDimensionalCoverSource (s.space.toRepresentation.comp L.subtype))
    (hloc : ∀ D, IsBestOffender (subspaceImageRepresentation ρ s.space.toSubmodule) D →
      D ≤ restrictedSubgroup ρ s.space.toSubmodule L) :
    Nonempty (ProductConfiguration ρ L s.space) := by
  let := hyp.finite_module
  obtain ⟨hf, hz⟩ := fourCover_faithful_center s cover
  exact configuration_of_offender_image ρ hyp.generated s.space L hf hz hloc
    (Or.inl (fourCover_supplement s hyp.faithful hA hAL cover))

/-- B.5.10 from the exact preceding B.5.9 alternative. Here W is literally
`[V,L]`, and H is L except in the marked symmetric-five case, where it is LA.
All normality, faithfulness, localization and supplement premises of the
product construction are discharged. The commutator identity is retained
from the source reduction; the preceding alternative already supplies the
module facts needed at this step. -/
theorem configuration_of_componentActionCase (hyp : FFHypothesis K ρ)
    {A L H : Subgroup G} [L.Normal] (hA : IsMinimalBestOffender ρ A)
    (hL : IsComponent G L) (_hLA : ⁅L, A⁆ = L) (s : MovedSection ρ L)
    (hc : ComponentActionCase ρ A L s H) :
    Nonempty (ProductConfiguration ρ H s.space) := by
  cases hc with
  | linearTwo F hn hsyl hs =>
      exact configuration_linearTwo hyp s F hn hsyl hs (Localization.linearTwo hyp hL s F hn)
  | symmetricFive e _ hs =>
      exact symmetricFive_configuration s e hyp hs
  | doubleThree F ho hn hAL _ =>
      exact configuration_doubleThree hyp s F ho hA.1 hAL hn
        (Localization.doubleThree hyp s F ho hn)
  | naturalThree F ho hn _ =>
      exact configuration_naturalThree hyp s F ho hn (Localization.naturalThree s F ho hn)
  | fourCover cover _ hAL _ =>
      exact configuration_fourCover hyp s hA.1 hAL cover (Localization.fourCover hL s cover)

/-- Apply B.5.10 to the parent's actual B.5.9 witness, producing the full
component-reduction conclusion. Only construction of the preceding action
alternative remains with that parent; there is no separate product premise. -/
theorem conclusion_of_componentActionCase (hyp : FFHypothesis K ρ)
    {A L H : Subgroup G} [L.Normal] (hA : IsMinimalBestOffender ρ A)
    (hL : IsComponent G L) (hLA : ⁅L, A⁆ = L) (s : MovedSection ρ L)
    (hc : ComponentActionCase ρ A L s H) : Nonempty (Conclusion ρ) := by
  obtain ⟨c⟩ := configuration_of_componentActionCase hyp hA hL hLA s hc
  exact ⟨{
    offender := A
    minimal := hA
    component := L
    isComponent := hL
    component_normal := inferInstance
    commutator_eq := hLA
    sectionData := s
    first := H
    actionCase := hc
    productConfiguration := c }⟩

end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.ProductGeometry
