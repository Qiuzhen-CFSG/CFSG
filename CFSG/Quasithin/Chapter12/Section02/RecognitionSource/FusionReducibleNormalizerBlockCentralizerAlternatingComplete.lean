module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockCentralizerAlternatingResidual
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockCentralizerAlternatingMovedImage
public import Theory.Representation.OrthogonalFourMinusRankOne.InnerClassification.Conjugacy
/-!
# Completion of the alternating-six surviving-block branch

The intrinsic fixed-line argument constructs coordinates for the actual
local residual. Conjugating the whole quotient into those coordinates
preserves quadraticity of the moved omega module. Its image is the
complementary transposition, so the invariant-cubic argument constructs
all invariant-core geometry and yields the terminal contradiction.

The original alternating centralizer contract and the retained marking
and invariant-core contracts are discharged here. The final application
leaves only the nonalternating local invariance and terminal branches with
qt-d-12216-normalizer-block-centralizer; the external reduction remains
with qt-d-12216-sylow-normalizer. No model, movement, or geometry premise
remains in the alternating branch.
Source: Aschbacher–Smith 3.3.25–31, printed pp.599–602.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
private theorem moved_image_of_conjugated_residual
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hb : ChapterC.IsAlternatingBlock L 6)
    {d : G} (hd : d ∈ normalizer (T : Set G))
    (hmove : ¬ (blockOmegaModule T L).map (MulAut.conj d⁻¹).toMonoidHom ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hnormal : blockLocalResidual T L ⊔ (T : Subgroup G) ≤ normalizer
      ((blockOmegaModule T L).map (MulAut.conj d⁻¹).toMonoidHom : Set G))
    {ρ : ChapterC.AlternatingSixBlockAction.Actor →*
      MulAut (Multiplicative ChapterC.AlternatingSixBlockAction.Vector)}
    (m : ChapterC.BlockModuleModel L ρ)
    (hρ : ∀ g v, (ρ g v).toAdd =
      BinaryPermutation.naturalRepresentation (Fin 6) g v.toAdd)
    (g : S)
    (hX : ((blockLocalResidual T L).subgroupOf (L ⊔ (T : Subgroup G))).map
      ((MulAut.conj g).toMonoidHom.comp
        (ChapterC.AlternatingSixBlockAction.joinPermutation D.sylow_normalizes_component m hρ)) = K)
    (hT : ((T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G))).map
      ((MulAut.conj g).toMonoidHom.comp
        (ChapterC.AlternatingSixBlockAction.joinPermutation D.sylow_normalizes_component m hρ)) ≤ H1) :
    (((blockOmegaModule T L).map (MulAut.conj d⁻¹).toMonoidHom).subgroupOf
      (L ⊔ (T : Subgroup G))).map
      ((MulAut.conj g).toMonoidHom.comp
        (ChapterC.AlternatingSixBlockAction.joinPermutation D.sylow_normalizes_component m hρ)) =
        zpowers swap45 := by
  let H := L ⊔ (T : Subgroup G)
  let A := (blockOmegaModule T L).map (MulAut.conj d⁻¹).toMonoidHom
  let q₀ := ChapterC.AlternatingSixBlockAction.joinPermutation D.sylow_normalizes_component m hρ
  let q := (MulAut.conj g).toMonoidHom.comp q₀
  let E := (A.subgroupOf H).map q
  have hAT : A ≤ (T : Subgroup G) := by
    rw [← mem_normalizer_iff_map_conj_eq.mp ((normalizer _).inv_mem hd)]
    exact map_mono (blockOmegaModule_le_sylow h)
  have hAH : A ≤ H := hAT.trans le_sup_right
  let := blockOmegaModule_elementary h
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map (MulAut.conj d⁻¹).toMonoidHom
  let : IsElementaryAbelian 2 (A.subgroupOf H) := IsElementaryAbelian.subgroupOf hAH
  have hE : IsElementaryAbelian 2 E := IsElementaryAbelian.map q
  have hEH : E ≤ H1 := (map_mono (comap_mono hAT)).trans hT
  have hXA : blockLocalResidual T L ≤ normalizer (A : Set G) := le_sup_left.trans hnormal
  have hnorm : K ≤ normalizer (E : Set S) := by
    rw [← hX]
    exact (map_mono ((comap_mono hXA).trans (le_normalizer_comap H.subtype))).trans
      (le_normalizer_map q)
  have hUA : (ChapterC.blockU L).map L.subtype ≤ normalizer (A : Set G) :=
    (blockU_le_blockOmegaModule h D hescape hb.2.1).trans
      ((blockOmegaModule_le_sylow h).trans (le_sup_right.trans hnormal))
  have hq₀ := ChapterC.AlternatingSixBlockAction.joinPermutation_isQuadratic_of_normalizes
    D.sylow_normalizes_component m hρ A inferInstance hUA
  have hq : Representation.BinaryOffender.IsQuadratic (BinaryPermutation.naturalRepresentation (Fin 6)) E := by
    change Representation.BinaryOffender.IsQuadratic _ ((A.subgroupOf H).map
      ((MulAut.conj g).toMonoidHom.comp q₀))
    rw [← map_map]
    exact (Representation.OrthogonalFourMinus.RankOne.InnerTransport.quadratic_conj_iff
      _ _ g).mpr hq₀
  have hle : E ≤ zpowers swap45 := elementary_quadratic_normalized_K_le_swap45 E hE hEH hnorm hq
  have hne : E ≠ ⊥ := by
    intro he
    have hk : A.subgroupOf H ≤ q.ker := (Subgroup.map_eq_bot_iff _).mp he
    have hker : q.ker = ((L ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf H :=
      (MonoidHom.ker_comp_of_injective q₀ (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).trans
          (ChapterC.AlternatingSixBlockAction.joinPermutation_kernel
            D.sylow_normalizes_component m hρ hb.2.1)
    rw [hker] at hk
    apply hmove
    intro a ha
    exact hk (show (⟨a,hAH ha⟩ : H) ∈ A.subgroupOf H from ha)
  obtain ⟨g,hg,hgne⟩ := E.bot_or_exists_ne_one.resolve_left hne
  have hgcases : g = 1 ∨ g = swap45 := by
    have hs : orderOf swap45 = 2 :=
      (show swap45.IsSwap from ⟨4,5,by decide,rfl⟩).orderOf
    have hm := mem_zpowers_iff_mem_range_orderOf.mp (hle hg)
    obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hm
    have hn2 : n < 2 := by simpa only [hs] using Finset.mem_range.mp hn
    have hn01 : n = 0 ∨ n = 1 := by omega
    rcases hn01 with rfl | rfl
    · exact Or.inl (by simpa only [pow_zero] using he.symm)
    · exact Or.inr (by simpa only [pow_one] using he.symm)
  have he : g = swap45 := hgcases.resolve_left hgne
  exact le_antisymm hle (zpowers_le.mpr (he ▸ hg))


/-- Construct the complete six-letter marking for the actual moving element. -/
theorem alternating_six_local_marking_original
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥) (hb : ChapterC.IsAlternatingBlock L 6)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    {d : G} (hd : d ∈ normalizer (T : Set G))
    (hmove : ¬ (blockOmegaModule T L).map (MulAut.conj d⁻¹).toMonoidHom ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hnormal : blockLocalResidual T L ⊔ (T : Subgroup G) ≤ normalizer
      ((blockOmegaModule T L).map (MulAut.conj d⁻¹).toMonoidHom : Set G)) :
    Nonempty (AlternatingSixLocalMarking T L d) := by
  obtain ⟨ρ, ⟨m⟩, hρ⟩ := hb.2.2
  obtain ⟨g,hg⟩ := alternating_six_residual_image_conjugate h D hescape hb m hρ
  let H := L ⊔ (T : Subgroup G)
  let q₀ := ChapterC.AlternatingSixBlockAction.joinPermutation D.sylow_normalizes_component m hρ
  let q := (MulAut.conj g).toMonoidHom.comp q₀
  have hX : ((blockLocalResidual T L).subgroupOf H).map q = K := by
    rw [← map_map]
    exact hg
  have hi := blockLocalInvariance_of_alternating h D hfixed hb
  have hTX : (T : Subgroup G) ≤ normalizer (blockLocalResidual T L : Set G) :=
    (T : Subgroup G).le_normalizer.trans ((hi.1 (Or.inl hb)).1)
  have hT : ((T : Subgroup G).subgroupOf H).map q ≤ H1 := by
    have hn : ((T : Subgroup G).subgroupOf H).map q ≤
        normalizer (((blockLocalResidual T L).subgroupOf H).map q : Set S) :=
      (map_mono ((comap_mono hTX).trans (le_normalizer_comap H.subtype))).trans
        (le_normalizer_map q)
    rw [hX] at hn
    exact hn.trans normalizer_K_le_H1
  exact ⟨{
    quotient := q
    kernel := (MonoidHom.ker_comp_of_injective q₀ (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).trans
        (ChapterC.AlternatingSixBlockAction.joinPermutation_kernel
          D.sylow_normalizes_component m hρ hb.2.1)
    local_image := hX
    sylow_image := hT
    moved_image := moved_image_of_conjugated_residual h D hescape hb hd hmove hnormal m hρ g hX hT }⟩

/-- The complete marking producer required by the retained geometric API. -/
theorem alternatingSixLocalMarkingSource : AlternatingSixLocalMarkingSource T L V := by
  intro h D _ _ hfixed hescape _ hb d _ hd _ hmove hnormal
  exact alternating_six_local_marking_original h D hfixed hb hescape hd hmove hnormal

/-- Source invariant-core geometry, with its cubic subgroup and all local
invariance and quotient images constructed by the preceding proofs. -/
theorem alternatingInvariantCoreGeometrySource : AlternatingInvariantCoreGeometrySource T L V :=
  alternatingInvariantCoreGeometrySource_of_six_markings alternatingSixLocalMarkingSource

/-- Original alternating-block inputs give the Sylow normalizer conclusion
without additional geometry, model or movement premises. -/
theorem sylow_normalizer_le_of_alternating_block
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥) (hb : ChapterC.IsAlternatingBlock L 6) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) := by
  by_contra hescape
  have hi := blockLocalInvariance_of_alternating h D hfixed hb
  obtain ⟨d,ho,hd,hout,hmove,hnormal,_⟩ :=
    exists_odd_alternating_omega_movement h D hescape hi hb
  obtain ⟨marking⟩ := alternating_six_local_marking_original h D hfixed hb hescape hd hmove hnormal
  exact false_of_alternating_six_marking_original h D hfixed hb ho hd hout marking

/-- Discharge the exact alternating source contract for the final block assembly. -/
theorem alternatingBlockCentralizerSource : AlternatingBlockCentralizerSource T L V := by
  intro h D _ _ hfixed hescape _ hb
  exact (hescape (sylow_normalizer_le_of_alternating_block h D hfixed hb)).elim

/-- Apply the completed alternating branch to the original normalizer
consumer. Final assembly retains the nonalternating source obligations. -/
theorem sylow_normalizer_le_of_remaining_nonalternating_sources
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple) (hnone : NoEscape L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (reduction : BlockReductionSource T L V)
    (localSource : BlockLocalInvarianceSource T L V)
    (nonalternating : NonalternatingBlockCentralizerSource T L V) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) :=
  sylow_normalizer_le_of_local_block_branches h D structural hnone hfixed reduction
    localSource nonalternating alternatingBlockCentralizerSource

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
