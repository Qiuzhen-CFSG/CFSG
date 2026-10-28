module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.Assembly.SymplecticFour.MarkedAction.NaturalSection.Rows
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.Assembly.SymplecticFour.MarkedAction.NaturalSection.Products
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.Assembly.SymplecticFour.MarkedAction.NaturalSection.FieldTransport
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction.FlagTypes.ComponentAction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.LocalStructure.KernelControl
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.Assembly.SymplecticFour.MarkedAction.Normalization

/-!
# Natural coordinates on the actual symplectic plus-component section

Restrict the faithful W_K action to its best-offender subgroup. The published
component preparation puts the literal K⁺ inside this subgroup as a normal
component. The full adequate B.5.6 alternatives then apply: its quasisimple
branch gives the natural symplectic row, and all product, outer and hyperplane
branches are excluded by their actual component groups. Canonical restriction
identifies this section with plusComponentSection. The group order recovers
the field cardinality, and a field isomorphism transports both vectors and
matrices to the specified F.

The resulting ActionEquiv has an arbitrary group marking, including either
graph orientation. The final application supplies exactly the natural-section
premise of flagPreimages_normalized_of_natural for both literal preimages.
No natural action or complement on the whole W_K is assumed. The genuine
universal B.5 input remains explicit, as authorized for this extraction;
its global discharge belongs to the source-classification assembly.

Source: Aschbacher–Smith B.5.1, B.5.6, and the paragraph before 13.6.14
and Lemma 13.6.19, printed pp.99, 105 and 929–931, combined manuscript
of 1 March 2004.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.Assembly.SymplecticFour.MarkedAction.NaturalSection
open ComponentSelection ChapterB.QuasisimpleSource ChapterB.SourceInduction

/-- The complete adequate alternatives on a specified symplectic component
leave precisely its natural moved quotient. -/
theorem natural_of_classifier {D V F : Type*} [Group D] [Finite D]
    [AddCommGroup V] [Module (ZMod 2) V] [Field F] [Finite F]
    {ρ : Representation (ZMod 2) D V} {C : Subgroup D}
    (hC : IsComponent D C) {m : ℕ} (hF : Nat.card F = 2 ^ m) (hm : 1 < m)
    (mark : C ≃* Sp F) (s : MovedSection ρ C)
    (h : Nonempty (ProjectiveLine.QuasisimpleSourceConclusion ρ C) ∨
      Nonempty (SourceTwoFactorCase ρ) ∨ Nonempty (ChapterB.OuterSixThreeShape D) ∨
      Nonempty (HyperplaneCase ρ)) :
    ∃ E : BinaryField, Nonempty (ActionEquiv (s.action.comp C.subtype) (binarySymplectic E)) := by
  rcases h with h | h | h | h
  · obtain ⟨c⟩ := h
    exact natural_of_quasisimple hF hm mark s c
  · obtain ⟨c⟩ := h
    exact (no_twoFactors hF hm mark hC c).elim
  · obtain ⟨c⟩ := h
    exact (no_outerSixThree hF hm mark hC c).elim
  · obtain ⟨c⟩ := h
    exact (no_hyperplane hF hm mark hC c).elim

universe u
variable {G : Type u} [Group G] [Finite G]
variable (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
variable [IsElementaryAbelian 2 (Uv z v)]

/-- Extract the actual natural action from the full universal B.5 input.
The elementary structure on W_K is inherited from W_K ≤ Uᵥ. -/
theorem plus_component_natural
    {𝒦 : GroupClass.{u}} (source : AdequateClassificationInput.{u,u} 𝒦)
    (hSQ : IsSQTK 𝒦 (Gv v)) (hK : K ∈ Yz L T z v)
    (hn : Tv T v ≤ normalizer (K : Set G))
    (hU : Uv z v ≤ (Gv v).pCoreIn 2)
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hcore : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F] {m : ℕ}
    (hF : Nat.card F = 2 ^ m) (hm : 1 < m)
    (e : plusImage K L T z v hL hz K ≃* Sp F) :
    letI : IsElementaryAbelian 2 (WK K L T z v) :=
      IsElementaryAbelian.of_le (WK_le_Uv K L T z v hK.1.1)
    let C := plusImage K L T z v hL hz K
    let s := LinearThree.MarkedAction.plusComponentSection K L T z v hL hz hK hn
    Nonempty (ActionEquiv (s.action.comp C.subtype)
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2))) := by
  let : IsElementaryAbelian 2 (WK K L T z v) :=
    IsElementaryAbelian.of_le (WK_le_Uv K L T z v hK.1.1)
  intro C s
  let ρ := LinearThree.MarkedAction.plusRepresentation K L T z v hL hz
  let I := offenderSubgroup ρ
  have hd := LinearThree.MarkedAction.plus_component_offender_data
    K L T z v hL hz hK hn hU hSyl hcore
  have hCI : C ≤ I := hd.1
  let t := LinearThree.MarkedAction.ComponentAction.restrictSection s I hCI
  obtain ⟨E, ⟨c⟩⟩ := natural_of_classifier hd.2.2 hF hm
    ((subgroupOfEquivOfLe hCI).trans e) t
    (LinearThree.MarkedAction.plus_component_classifier_cases
      K L T z v hL hz source hSQ hK hn hU hSyl hcore)
  let a := LinearThree.MarkedAction.ComponentAction.restrictionActionEquiv s I hCI
  let b : ActionEquiv (s.action.comp C.subtype) (binarySymplectic E) :=
    { groupEquiv := a.groupEquiv.symm.trans c.groupEquiv
      linearEquiv := c.linearEquiv
      intertwines := fun g w => c.intertwines (a.groupEquiv.symm g) w }
  exact natural_over_field hF (by omega) e E b

/-- The permitted ambient source hypotheses discharge SQTK and the trivial
plus two-core. Neither A.3.6 nor a generalized-Fitting equality is needed for
this representation extraction. -/
theorem source_natural_section
    (source : AdequateClassificationInput.{u,u} KnownSimple.IsKnownSimple)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F] {m : ℕ}
    (hF : Nat.card F = 2 ^ m) (hm : 1 < m) (hv : orderOf v = 2)
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (hU : Uv z v ≤ (Gv v).pCoreIn 2)
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hW : WK K L T z v ∈ Chapter6.Source.reducedFamily (plusActor K L T v))
    (e : plusImage K L T z v hL hz K ≃* Sp F) :
    letI : IsElementaryAbelian 2 (WK K L T z v) :=
      IsElementaryAbelian.of_le (WK_le_Uv K L T z v hK.1.1)
    let C := plusImage K L T z v hL hz K
    let s := LinearThree.MarkedAction.plusComponentSection K L T z v hL hz hK hn
    Nonempty (ActionEquiv (s.action.comp C.subtype)
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2))) :=
  plus_component_natural K L T z v hL hz source (hG.involution_centralizer_sqtk hv)
    hK hn hU hSyl
    (LinearThree.LocalStructure.plus_twoCore_eq_bot_of_reduced K L T z v hL hz hW) hF hm e

/-- Actual consumer application: the extracted section supplies the natural
coordinates needed to normalize both published Sp₄ parabolic preimages. -/
theorem source_flagPreimages_normalized
    (source : AdequateClassificationInput.{u,u} KnownSimple.IsKnownSimple)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F] {m : ℕ}
    (hF : Nat.card F = 2 ^ m) (hm : 1 < m) (hv : orderOf v = 2)
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (hU : Uv z v ≤ (Gv v).pCoreIn 2)
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hW : WK K L T z v ∈ Chapter6.Source.reducedFamily (plusActor K L T v))
    (e : plusImage K L T z v hL hz K ≃* Sp F)
    (hmark : ((Tv T v).subgroupOf K).map (modelMap K L T z v hL hz e) ≤ unipotent) :
    Tv T v ≤ normalizer (pointPreimage K L T z v hL hz e : Set G) ∧
      Tv T v ≤ normalizer (planePreimage K L T z v hL hz e : Set G) := by
  let : IsElementaryAbelian 2 (WK K L T z v) :=
    IsElementaryAbelian.of_le (WK_le_Uv K L T z v hK.1.1)
  exact flagPreimages_normalized_of_natural K L T z v hL hz hF hm hK hn e hmark
    (source_natural_section K L T z v hL hz source hG hF hm hv hK hn hU hSyl hW e)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.Assembly.SymplecticFour.MarkedAction.NaturalSection
