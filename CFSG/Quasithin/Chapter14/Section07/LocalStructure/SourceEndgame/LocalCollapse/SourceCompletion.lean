module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse.SourceCompletion.Centralizer
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse.ProjectiveGaschutz
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse.NaturalRigidity.Displacement
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse

/-!
# The completed local collapse in14.7.74

The marked Steinberg splitting, both Gaschütz commutator arguments and
natural-extension displacement are constructed on the original groups.
Thus the genuine preceding71–73 data suffice for all74 conclusions and
the actual Ru center and centralizer identities. The following source
assembly constructs these preceding records from the same critical choice.

Source: Aschbacher–Smith,14.7.74–75,printed pp.1077–1078.
-/

public section
noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse.SourceCompletion
open Chapter12.Section08 CriticalFusion.Source
open CriticalFusion.Source.Rechoice.LocalGeometry.Preparation
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

/-- All original74 conclusions, with the point identities needed by75. -/
structure Conclusion74 (d : Data T L V F W) : Prop where
  self_normalizing : normalizer (L : Set G) = L
  core : S L F = (normalizer (L : Set G)).pCoreIn 2
  residual_product : F.H = K F ⊔ (T : Subgroup G)
  core_eq : F.H.pCoreIn 2 = (K F).pCoreIn 2
  sylow_center : ChapterJ.sylowCenter T = F.Vi 1
  point_centralizer : F.H = ChapterJ.centralizerOfSylowCenter T
  span_card : Nat.card (S L F) = 2 ^ 11
  core_card : Nat.card (F.H.pCoreIn 2) = 2 ^ 11

/-- The74 conclusion from genuine preceding source inputs, with every module
step discharged and all groups and quotient maps unchanged. -/
theorem source_lemma_14_7_74 (d : Data T L V F W)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (a : Prior d) (c : CriticalPath (L := L) F) (e : ChiefFactors.Earlier d c)
    (mark : UpperMarking d) (hcomm : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1) :
    Conclusion74 d := by
  have hKC := QC_K_le_U d structural a c e mark hcomm
  have hKQL := K_centralizes_QL d structural a mark hKC
  obtain ⟨hm,hs,hh,hp,hz,hc,hS,hQ⟩ := source_conclusions_of_module_steps d a
    (Q_eq_QC_sup_S d a) hKC hKQL
    (fun hQL hlt => NaturalRigidity.Displacement.QC_parabolic_displacement d a hKC hQL hlt)
  exact ⟨hm,hs,hh,hp,hz,hc,hS,hQ⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse.SourceCompletion
