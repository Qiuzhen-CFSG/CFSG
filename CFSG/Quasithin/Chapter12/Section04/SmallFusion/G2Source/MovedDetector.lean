module

public import Theory.Representation.G2BinaryOffenderDetector
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.MovedCentralizerCover
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.FixedLifting
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockCentralizerG2Detector

/-!
# The fixed-space detector for the actual moved G₂ module

A short-root involution in the full normalizer image detects the fixed space
of the moving offender. Lift it through that same actor and use fixed lifting
to retain the central line of V. The source factorization then extends the
detector to Q=O₂(LT), with the original conjugate Qᵈ and its actual elements.
This supplies the detector premise of the full maximum-family terminal proof.
Source: Aschbacher--Smith 3.3.28 and B.2.21, pp.601,82--83.
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
local notation "𝔽" => ZMod 2

/-- One actual element of the moving chosen module has exactly the same
centralizer on V as that entire module. -/
theorem moved_chosen_fixed_detector
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction (OrthogonalCover.action 𝔽))
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    {d : G} (hd : d ∈ normalizer (T : Set G))
    (hmove : ¬ V.map (MulAut.conj d).toMonoidHom ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    ∃ a ∈ V.map (MulAut.conj d).toMonoidHom,
      V ⊓ centralizer (V.map (MulAut.conj d).toMonoidHom : Set G) =
        V ⊓ centralizer ({a} : Set G) := by
  obtain ⟨b, ψ, hψ, _⟩ := exists_normalizer_full_g2_actor_marked h D structural e hne
  let N := normalizer (L : Set G)
  let B := V.map (MulAut.conj d).toMonoidHom
  have hBN : B ≤ N :=
    ((map_mono D.le_sylow).trans (mem_normalizer_iff_map_conj_eq.mp hd).le).trans
      D.sylow_normalizes_component
  let A := (B.subgroupOf N).map ψ
  have ho : IsOffender (traceZeroAction 𝔽) A :=
    (moved_full_actor_offender_image h D structural e hne b ψ hψ hd hmove).1
  have hon := (OrthogonalCover.BinaryOffenders.offender_iff_natural A).mp ho
  obtain ⟨c, hc, hfix⟩ := BinaryModelOffenders.natural_offender_exists_fixed_detector A hon
  obtain ⟨a, ha, hca⟩ := hc
  refine ⟨a.val, ha, le_antisymm ?_ ?_⟩
  · exact inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.mpr ha))
  · rintro x ⟨hxV, hxa⟩
    refine ⟨hxV, ?_⟩
    intro y hy
    have hfixed : action 𝔽 (ψ a) (mk 𝔽 (b ⟨x, hxV⟩).toAdd) =
        mk 𝔽 (b ⟨x, hxV⟩).toAdd :=
      (normalizer_actor_mem_centralizer_iff_natural_fixed b ψ hψ a ⟨x, hxV⟩).mp hxa
    rw [hca] at hfixed
    have hw : mk 𝔽 (b ⟨x, hxV⟩).toAdd ∈ fixedSpace (Atlas.G2.NaturalOffenders.binaryNatural (F := ZMod 2)) A := by
      rw [hfix, mem_fixedSpace_zpowers_iff]
      exact hfixed
    have hyN : y ∈ N := hBN hy
    have hyA : ψ ⟨y, hyN⟩ ∈ A := mem_map_of_mem ψ hy
    have hh := hw ⟨ψ ⟨y, hyN⟩, hyA⟩
    have hc := (normalizer_actor_mem_centralizer_iff_natural_fixed b ψ hψ
      ⟨y, hyN⟩ ⟨x, hxV⟩).mpr hh
    exact (mem_centralizer_singleton_iff.mp hc).symm

/-- The same actual element detects the centralizer of the conjugate whole
core on Q. The source cover, index, and elementarity inputs are internal. -/
theorem moved_chosen_core_fixed_detector
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction (OrthogonalCover.action 𝔽))
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    {d : G} (hd : d ∈ normalizer (T : Set G))
    (hmove : ¬ V.map (MulAut.conj d).toMonoidHom ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    ∃ a ∈ V.map (MulAut.conj d).toMonoidHom,
      (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ centralizer
          (((L ⊔ (T : Subgroup G)).pCoreIn 2).map (MulAut.conj d).toMonoidHom : Set G) =
        (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ centralizer ({a} : Set G) := by
  obtain ⟨a, ha, hfix⟩ := moved_chosen_fixed_detector h D structural e hne hd hmove
  have hb := g2Two_block_of_weyl_model h D hescape e
  have hV := chosen_eq_blockU D hb.short
  have hQe := (core_product_and_elementary_of_moved_chosen h D structural e hne
    hescape hd hmove).2.1
  have hfactor := core_eq_chosen_sup_moved_centralizer h D structural e hne hescape hd hmove
  have hf : (L ⊔ (T : Subgroup G)).pCoreIn 2 = (ChapterC.blockU L).map L.subtype ⊔
      ((L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ centralizer
        (((ChapterC.blockU L).map L.subtype).map (MulAut.conj (d⁻¹)⁻¹).toMonoidHom : Set G)) := by
    simpa only [inv_inv, ← hV] using hfactor
  have ha' : a ∈ ((ChapterC.blockU L).map L.subtype).map
      (MulAut.conj (d⁻¹)⁻¹).toMonoidHom := by
    simpa only [inv_inv, ← hV] using ha
  have hfix' : (ChapterC.blockU L).map L.subtype ⊓ centralizer
        (((ChapterC.blockU L).map L.subtype).map (MulAut.conj (d⁻¹)⁻¹).toMonoidHom : Set G) =
      (ChapterC.blockU L).map L.subtype ⊓ centralizer ({a} : Set G) := by
    simpa only [inv_inv, ← hV] using hfix
  refine ⟨a, ha, ?_⟩
  simpa only [inv_inv] using g2Two_local_core_fixed_detector_of_factorization D hb
    ((normalizer (T : Set G)).inv_mem hd) hQe hf a ha' hfix'

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
