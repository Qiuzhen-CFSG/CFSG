module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.OrderTwo
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.OrderTwo.SourceActors
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.OrderTwo.SourceQuadratic
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.OrderTwo.CriticalIntersections.Construction
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.SourceCompletion.ModuleSeparation
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.SourceFusion
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ActorPlacement
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.CoreProduct
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.StarSylow
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.Source
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
/-!
# The original source inputs to 14.7.69

Re-mark the target natural quotient once to identify its upper root group;
the original group, path, section coordinates and action are retained.
The source constructs the two chart actors, section centralizer, module
separation, genuine dual pairing, point commutator, critical images,
quadratic action and fusion of z. The residual normalizer supplies the
uniqueness of U₀-conjugates after the centralizer conclusion of 14.7.68(2).
The complete order-two argument then applies to the same critical path.

The genuinely earlier 14.7.39/F.9.17 reversed-path implication and the
separate centralizer clause of 14.7.68(2) remain explicit. Their producers
are the source-reversal family and the fixed-centralizer component family.
Original 12.2.2, faithful classification, 13.3.2, 14.7.10 and 14.7.31 are
also retained; no chart, duality, image or order-two conclusion is assumed.

Source: Aschbacher–Smith 14.7.66–69, printed pp.1070–1073.
-/

public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Subgroup Representation Chapter12.Section08 ResidualNormalizer Rechoice.Goldschmidt
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Rechoice.Goldschmidt.LeftChiefFactors.BorelRefinements
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

theorem Data.order_two_of_original_source (d : Data T L V F W)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (modules : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
    (baumann : LocalControl.Earlier14710.{u}) (weakClosure : Theorem14731.{u})
    (symmetry : d.EarlierSymmetry)
    (hcentralizer68 : ∀ u : F.U, (u : G) ∈ d.U₀ → (u : G) ≠ 1 →
      d.FixedModuloPoint u → centralizer ({(u : G)} : Set G) ≤ F.H)
    (c : CriticalPath (L := L) F) (selection : c.RankSelection) :
    Nat.card (star F c.Uα) = 2 := by
  let d' := upperRemark d structural
  have uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro X _ _ hX S K hK
    exact Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
      (fun Y _ _ => ChapterA.Section02.theoremA_knownSimple (G := Y))
      (fun Y _ _ => ChapterA.Section02.theoremC_knownSimple (G := Y)) hX S hK
  have hc := d'.sectionCentralizer_of_earlier_setup structural uniqueness
  obtain ⟨X,aX,mX,hs⟩ := CriticalIntersections.exists_sourceDuality d' hc
  let := aX
  let := mX
  obtain ⟨s⟩ := hs
  have himage := (d'.source_core_product_of_source1332 structural uniqueness modules).2
  have earlier := d'.source_earlierImages structural c himage (d'.source_Ri_star_sylow structural)
  have hcomm := d'.U_core_commutator_eq_point_of_source1332 modules structural uniqueness
  have hn := (d'.normalizer_K_eq_H_of_known_simple_source structural faithful modules baumann weakClosure).1
  have hsym : d'.EarlierSymmetry := by
    intro a ha hs hr
    exact symmetry a ha (a.sourceSelection_of_rank d hs.toRankSelection) hr
  refine d'.lemma_14_7_69 hc (Rechoice.SourceCompletion.moduleSeparation d') s
    (fun a ha b => source_criticalChart_localActors d structural hc a ha b)
    hsym hcomm
    (d'.fusion_z_of_known_simple_source structural faithful modules baumann weakClosure)
    ?_ c earlier (c.sourceSelection_of_rank d' selection) (d'.source_reciprocal_placement c)
  intro u hu hne hfix
  have hcent := hcentralizer68 u hu hne hfix
  exact ⟨hcent,fun g hg => d'.U₀_conjugate_eq_of_centralizer_le hn u g hcent hg⟩
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
