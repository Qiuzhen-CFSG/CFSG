module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryThompsonEscape
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryThompsonRelativePlanes

/-!
# The actual cubic plane in the outer Thompson alternative

The group-only outer A₆–C₃ configuration supplies a component of three-rank
at least two and excludes quasisimple generalized Fitting. Reapplying the
proved B.5.7 cover reduction, with the earlier known-simple inputs discharged,
therefore reaches its noncentral module calculation. The actual offender
endgame makes the whole three-core move a plane. This uses no fixed-space
splitting from the legacy B.5.6(4) statement.

For the original reduced orbit, the three-core is characteristic in the
normal Thompson image and is consequently ambient normal. Odd-order
averaging supplies the plane's complement, and the original residual-plane
containment places its full inverse image in M. The actual chosen-module
application is NonFFSourceDoubledBinaryOuterThreeCore; the remaining odd-core
and quotient-component branches and final assembly stay with
qt-d-1222-nonff-doubled.
Source: Aschbacher–Smith, B.5.7, printed p.106; proof of Proposition 7.7.3,
printed p.707, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOuterThreeCore
open ChapterB.SourceInduction ChapterB.QuasisimpleSource
open HighThreeRank HighThreeRank.ModuleCalculation
open HighThreeRank.CoverCentralizer.SourceConstruction
open HighThreeRank.ModuleCalculation.NaturalReduction.ModelComparison
universe u v

/-- The original B.5.7 moved-module proof supplies the cubic plane even
though the adequate outer group record does not assert a module splitting. -/
theorem threeCore_plane_of_outerShape
    {D : Type u} [Group D] [Finite D]
    {X : Type v} [AddCommGroup X] [Module (ZMod 2) X]
    (ρ : Representation (ZMod 2) D X)
    (hyp : FFHypothesis KnownSimple.IsKnownSimple ρ)
    (c : ChapterB.OuterSixThreeShape D) :
    Module.finrank (ZMod 2) (moved ρ (pCore 3 D)) = 2 := by
  have hA : SemisimpleInput KnownSimple.IsKnownSimple :=
    fun _ _ _ => ChapterA.Section02.theoremA_knownSimple
  have h36 : Chapter1.Section02.A36Input KnownSimple.IsKnownSimple :=
    ChapterA.SQTKStructure.a36Input_of_theoremsAC
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  have h4 := ChapterB.SourceClassification.irreducibleClassification_knownSimple
  have h1 := SourceCompletion.knownSimple_quasisimpleClassificationInput
    hA h36 h4 nonbinaryG2RootPairInput
  have h5 := ChapterB.PreparationSource.componentInput
    ChapterB.PreparationSource.componentNormalization hA h36 h4
  obtain ⟨d⟩ := PreciseMultiplierInputs.liftedCover_of_preparation ρ
    (coverInput_of_a36 h36) h5 hA h36 hyp c.first_isComponent c.first_three_rank
  rcases CoverCentralizer.reduction_of_liftedCover hyp c.first_isComponent
    c.first_three_rank d with ⟨hsq,hfit⟩ | hd
  · obtain ⟨hq,_⟩ := HighThreeRank.quasisimple_branch ρ h1 hyp c.first_isComponent hsq hfit
    exact (c.not_quasisimple_fitting hq).elim
  · obtain ⟨d⟩ := hd
    obtain ⟨A,hA,hm,_,_⟩ := exists_moving_offender ρ hyp c.first_isComponent d
    obtain ⟨r⟩ := reduced_of_threeFreePerfectKernels h1
      alternatingEight_threeFreePerfectKernels binaryG2_threeFreePerfectKernels
      ρ hyp c.first_isComponent c.first_three_rank d hA hm
    obtain ⟨m⟩ := NaturalReduction.model_of_reduced ρ hyp c.first_isComponent d hm r
    have hfix := NaturalCentralizers.threeCore_fixes_model ρ
      NaturalCentralizers.ConcreteModels.modelCommutants c.first_isComponent d m
    exact (NaturalCentralizers.source_offender_plane ρ hyp c.first_isComponent d hA hm hfix m).plane

open ChapterB.InternalThompsonAction DoubledBinaryThompson
open DoubledBinaryThompsonRelativePlanes

/-- The full three-core preimage in the original centralizer quotient lies
in M in the outer A₆–C₃ alternative. Ambient normality follows from its
characteristic inclusion in the normal Thompson image. -/
theorem outer_thompson_threeCore_preimage_contained
    {H : Type u} [Group H] [Finite H]
    (Y : Subgroup H) (hY : IsPReduced 2 Y) (R M : Subgroup H)
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hplanes : RelativePlaneFactorsContained Y hY R M) :
    let := hY.normal
    let := hY.elementary
    Nonempty (ChapterB.OuterSixThreeShape (thompsonImage Y)) →
      ((pCore 3 (thompsonImage Y)).map (thompsonImage Y).subtype).comap
        (actionMk Y) ≤ M := by
  let := hY.normal
  let := hY.elementary
  dsimp only
  intro hc
  obtain ⟨c⟩ := hc
  let J := thompsonImage Y
  let A := (pCore 3 J).map J.subtype
  let q := actionMk Y
  let : (Stellmacher.elementaryAbelianMaxJ (⊤ : Subgroup H)).Characteristic :=
    Stellmacher.elementaryAbelianMaxJ_top_characteristic
  let : J.Normal :=
    (inferInstance : (Stellmacher.elementaryAbelianMaxJ (⊤ : Subgroup H)).Normal).map q
      (QuotientGroup.mk'_surjective _)
  let : A.Normal := ConjAct.normal_of_characteristic_of_normal
  have hd : Module.finrank (ZMod 2) (moved (action Y) A) = 2 := by
    have hh := threeCore_plane_of_outerShape (thompsonAction Y)
      (thompson_hypothesis Y hH hY.quotient_pCore_eq_bot) c
    change Module.finrank (ZMod 2)
      (moved ((action Y).comp J.subtype) (pCore 3 J)) = 2 at hh
    rw [moved,subspaceCommutator_comp_map] at hh
    exact hh
  have ho : Odd (Nat.card A) := by
    rw [card_map_of_injective J.subtype_injective]
    obtain ⟨n,hn⟩ := (pCore_isPGroup : IsPGroup 3 (pCore 3 J)).exists_card_eq
    rw [hn]
    exact (by decide : Odd 3).pow
  have he : RegularCyclicNormalClosure.displacementSpan (action Y) A ⊤ =
      moved (action Y) A := by
    unfold moved subspaceCommutator RegularCyclicNormalClosure.displacementSpan
    congr 1
    ext v
    simp only [eq_comm]
  have hs := GoldschmidtONan.isCompl_fixed_moved_of_odd (ρ := action Y) ho
  rw [he] at hs
  exact hplanes A le_normalizer_of_normal le_normalizer_of_normal (map_subtype_le _) hd
    hs.symm.sup_eq_top

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOuterThreeCore
