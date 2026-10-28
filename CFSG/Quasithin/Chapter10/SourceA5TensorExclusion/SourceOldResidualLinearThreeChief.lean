module
public import CFSG.Quasithin.Chapter3.Section01.SourceStrictChief
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualLinearThreeCoreGeometry
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorOmegaCenterFree

/-!
# The actual small-ratio chief factor in the PSL₃(4) alternative

The original cubic geometry puts the entire tensor module in O₂(H).
Tensor non-FF and the genuine qrc source then make its H-conjugate span
elementary. Under the tensor ratio and nondual-FF inputs, local uniqueness
and the strict chief estimate select a noncentral chief factor with quadratic
ratio at most two. This is the literal chief action to which the remaining
PSL₃(4) representation exclusion must apply. Its kernel is proved to be
exactly O₂(H), using the original maximal-core equality.

The two tensor numerical inputs remain explicit; the theorem neither assumes
H-normality of the original module nor asserts irreducibility on the residual.
Source: Aschbacher--Smith9.2.7 and3.1.6, printed pp.731--732 and573--575.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender NoncentralChiefRefinement
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterB ChapterD ChapterD.UniqueFactor ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

theorem old_residual_linear_three_exists_small_chief
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (hK : (pResidual 2 H).IsCComponent)
    (hm : let hP := source_a5_hstar_minimal_parabolic D e m.sylow_not_normalizes_component hH
      ClassicalGroup.IsPSL (ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.sourceImage
        (ChapterB.minimalParabolicMax (T.subtype hH.1.1.2) hP) (pResidual 2 H)) 3 4)
    (hq : letI := m.fullModule_elementary
      (4 / 3 : ℝ≥0∞) ≤ quadraticRatio (imageRepresentation (sourceFullModuleNormalizer D)
        D.fullModule (inf_le_left.trans D.maximalLocal_normalizes_fullModule)))
    (hdual : ¬ SourceFullModuleDualFF D) :
    let U := (conjugateSpan H D.fullModule).subgroupOf H
    ∃ hU : IsElementaryAbelian 2 U, letI := hU
      ∃ (s : SeriesOn U) (i : Fin s.series.length), ¬ s.Central i ∧
        quadraticRatio (Representation.BinaryOffender.imageRepresentation
          (s.factorRepresentation i)) ≤ 2 := by
  let h := source_fullModule_qrcHypotheses D hH
  have hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → sourceFullModuleNormalizer D ≤ N →
      N = D.maximalLocal := fun N hN hle => source_fullModuleNormalizer_unique D hN hle
  let d := h.toQRCConfiguration (h.no_common_normal hu)
  have hV : D.fullModule ≤ twoCoreIn H :=
    m.old_residual_linear_three_fullModule_le_twoCore hH hlarge hK hm
  have hnf : letI := h.module_elementary
      ¬ IsFFModule (imageRepresentation (sourceFullModuleNormalizer D)
        D.fullModule h.module_normalized) :=
    m.fullModule_actionImage_notFF (sourceFullModuleNormalizer D)
      (le_sup_left.trans (source_localJoin_le_fullModuleNormalizer D)) inf_le_left
      (inf_le_left.trans D.maximalLocal_normalizes_fullModule)
  have hne : D.fullModule ≠ ⊥ := fun he => D.module_ne_bot
    (bot_unique ((le_componentOrbit D.moduleSubgroup D.maximalLocal).trans he.le))
  let U := (conjugateSpan H D.fullModule).subgroupOf H
  let := source_elementary_span_of_notFF d hV hnf
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    ((span_le_right_core d hV).trans (twoCore_le H))
  refine ⟨inferInstance,?_⟩
  exact h.exists_noncentral_chief_ratio_le_two_of_four_thirds D.simpleQTKE
    (D.lemma_3_2_3_uniqueness (source_module_nonsolvable_uniqueness D)).1 hu
    m.thompson_centralizes_fullModule hne hV hnf hq hdual

/-- Every noncentral chief action of the original span has exactly the actual two-core as kernel. -/
theorem old_residual_linear_three_chief_kernel_eq_twoCore
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (hK : (pResidual 2 H).IsCComponent)
    (hm : let hP := source_a5_hstar_minimal_parabolic D e m.sylow_not_normalizes_component hH
      ClassicalGroup.IsPSL (ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.sourceImage
        (ChapterB.minimalParabolicMax (T.subtype hH.1.1.2) hP) (pResidual 2 H)) 3 4)
    [IsElementaryAbelian 2 ((conjugateSpan H D.fullModule).subgroupOf H)]
    (s : SeriesOn ((conjugateSpan H D.fullModule).subgroupOf H))
    (i : Fin s.series.length) (hi : ¬ s.Central i) :
    (s.factorRepresentation i).ker = pCore 2 H := by
  let σ := s.factorRepresentation i
  let := s.factorRepresentation_irreducible i
  have hn : ∃ h w, σ h w ≠ w := by
    by_contra! hn
    apply hi
    rw [s.central_iff_action]
    intro h x
    exact congrArg Additive.toMul (hn h (Additive.ofMul x))
  let hP := source_a5_hstar_minimal_parabolic D e m.sylow_not_normalizes_component hH
  have hk : σ.ker ≤ minimalParabolicCore (T.subtype hH.1.1.2) hP :=
    minimalParabolic_source6a _ hP σ (irreducible_residual_not_le_ker σ hn)
  rw [m.old_residual_linear_three_core_eq_twoCore hH hlarge hK hm] at hk
  exact le_antisymm hk (normal_p_subgroup_le_ker σ _ pCore_isPGroup)


end CFSG.Quasithin.Chapter10.SourceA5TensorModel
