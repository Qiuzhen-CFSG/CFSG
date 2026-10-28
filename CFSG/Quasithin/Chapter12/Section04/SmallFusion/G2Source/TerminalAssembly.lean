module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.MovedDetector
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.FullFamily
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockCentralizerG2Detector

/-!
# The original binary G₂ terminal contradiction

The moved source supplies the odd subgroup, its escaping element, and the
factorization of the original two-core.  The actual moved module supplies a
singleton fixed-space detector, while the full-family bridge supplies the
common image for every maximal elementary subgroup of the local residual.
This module only transports those three facts to the literal
`blockLocalCore` interface and applies the existing terminal detector.

Source: Aschbacher--Smith 3.3.28, printed p.601, and B.2.21, pp.82--83.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
open Chapter12.Section02 Chapter12.Section02.RecognitionSource
open Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
open ChapterB.QuasisimpleSource Atlas.G2.Natural

universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
local notation "F" => ZMod 2

/-- The source odd-movement data closes the literal binary G₂ endpoint. -/
theorem false_of_moved_g2_source
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction (OrthogonalCover.action F))
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    False := by
  obtain ⟨_, B, hBN, hodd, d, hd, hout, hmove, _, _, _, hfactor⟩ :=
    exists_odd_moving_chosen_core_factorization h D structural e hne hescape
  have hQe := (core_product_and_elementary_of_escape h D structural e hne hescape).2.1
  have hb := g2Two_block_of_weyl_model h D hescape e
  have hU := chosen_eq_blockU D hb.short
  have hfactor' : (L ⊔ (T : Subgroup G)).pCoreIn 2 =
      (ChapterC.blockU L).map L.subtype ⊔
        ((L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ centralizer
          (((ChapterC.blockU L).map L.subtype).map
            (MulAut.conj d⁻¹).toMonoidHom : Set G)) := by
    simpa only [← hU] using hfactor
  obtain ⟨a, ha, hfix⟩ := moved_chosen_fixed_detector h D structural e hne
    (d := d⁻¹) ((normalizer (T : Set G)).inv_mem (hBN hd)) hmove
  have ha' : a ∈ ((ChapterC.blockU L).map L.subtype).map
      (MulAut.conj d⁻¹).toMonoidHom := by
    simpa only [← hU] using ha
  have hfix' : (ChapterC.blockU L).map L.subtype ⊓ centralizer
        (((ChapterC.blockU L).map L.subtype).map
          (MulAut.conj d⁻¹).toMonoidHom : Set G) =
      (ChapterC.blockU L).map L.subtype ⊓ centralizer ({a} : Set G) := by
    simpa only [← hU] using hfix
  obtain ⟨q, hker, hcommon⟩ :=
    G2FullFamilyBridge.Source.exists_full_family_common_image h D structural e hne
      hescape (hBN hd) hmove
  let q' : blockLocalCore T L →* Atlas.G2.Model F := q
  have hker' : q'.ker = ((L ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf
      (blockLocalCore T L) := hker
  have hcommon' : ∀ A ∈ Stellmacher.elementaryAbelianMaxSubgroups
      (⊤ : Subgroup (blockLocalCore T L)),
      ¬ A ≤ ((L ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf (blockLocalCore T L) →
      A.map q' = ((((L ⊔ (T : Subgroup G)).pCoreIn 2).map
        (MulAut.conj d⁻¹).toMonoidHom).subgroupOf (blockLocalCore T L)).map q' := hcommon
  exact false_of_g2_local_intrinsic_detector h D hne hb B hBN hodd d hd hout
    hQe hfactor' q' hker' a ha' hfix' hcommon'

/-- The original binary Weyl row forces Sylow-normalizer containment,
with only the source structural and action hypotheses. -/
theorem sylow_normalizer_le_of_g2_weyl_source
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction (OrthogonalCover.action F))
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) := by
  by_contra hescape
  exact false_of_moved_g2_source h D structural e hne hescape

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
