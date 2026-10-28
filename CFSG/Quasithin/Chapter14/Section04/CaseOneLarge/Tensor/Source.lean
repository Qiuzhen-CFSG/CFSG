module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Tensor.DeletedSize
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Tensor.NaturalSource

/-!
# Combining the two marked tensor constituents

The natural constituent uses the already constructed Partner and A₃
contradiction. The deleted constituent uses the literal mixed F.1.12
application. Thus both tensor alternatives are excluded under the same
existing numerical source input, without assuming a selected constituent,
a geometry callback or U = O₂(H). The original flag constructs its source
conjugator in the final consumer.

The mixed size theorem remains owned by `qt-d-tensor-mixed-size-bound`.
This conditional tensor assembly does not prove catalogue exhaustiveness,
the orthogonal exclusion, or the final 14.4.14 theorem.

Source: Aschbacher--Smith, 14.4.2(5), 14.4.10 and 14.4.13,
printed pp.1006,1010--1012.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension LargerDimension.Tensor LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : Subgroup Five} {hAD : AltFive ≤ D}
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

/-- Both tensor constituents are excluded, retaining the prescribed conjugator. -/
theorem source_tensor_contradiction_of_mixed_size (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (size : Chapter10.MixedZeroCore.MixedSizeInput G)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (c : CaseFiveCoordinates hAD (V := W) F.H F.U) : False := by
  rcases c.constituent_model with hnat | hdel
  · have hc := source_tensor_closure_card d earlier hq chosen structural alternatives F hne hZ c
    exact source_tensor_natural_contradiction d earlier hq chosen structural alternatives
      classification F hne hZ (by omega) g hg hgP hgH c hnat
  · exact source_tensor_deleted_contradiction_of_mixed_size d earlier hq chosen structural
      alternatives classification size F hne hZ g hg hgP hgH c hdel

/-- Eliminate the entire marked tensor row on the original flag. The source
conjugator is constructed; the only extra source theorem is the existing
mixed F.1.12 numerical input. -/
theorem source_tensor_exclusion_of_mixed_size (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (size : Chapter10.MixedZeroCore.MixedSizeInput G)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (c : CaseFiveCoordinates hAD (V := W) F.H F.U) : False := by
  obtain ⟨g, hg, hgP, hgH⟩ := exists_source_conjugator d earlier hq chosen structural F
  exact source_tensor_contradiction_of_mixed_size d earlier hq chosen structural alternatives
    classification size F hne hZ g hg hgP hgH c

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
