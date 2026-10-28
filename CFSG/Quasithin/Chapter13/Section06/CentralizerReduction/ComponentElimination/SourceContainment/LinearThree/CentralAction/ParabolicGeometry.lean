module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.SeedGeometry
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.Coordinates
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.Frattini

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.ComponentNormalizer
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.Thompson
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.SplitSeed

/-!
# The central branch of 13.6.20 in an actual doubled-natural marking

The full marked source setup extends the component's doubled action.
The offender calculation and B.2.20 identify J(T_v)⁺ and Baum(T)⁺ with
one concrete shear radical after a coherent coordinate change. The
Frattini lift restricted to K identifies N_K(Baum(T))⁺ with the full
line parabolic. The marked cubic seed has split-point coordinates with
the same actor. These constructions discharge both geometric premises
of `false_of_marked_seed_geometry`.

The final source application retains full Hypothesis 13.3.1, the actual
A₅ flag, genuine earlier local conclusions, and hypothetical centrality.
Its only representation input is the actual doubled-natural marking d0.
The enclosing CentralAction owner must produce d0 using B.5 and complete
the other module alternative; no later 13.6.22 result is used here.
The earlier local and component statements remain with their existing
section owners and are explicit in `false_of_source_doubled`.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of Lemma 13.6.20, printed p.931; Lemma B.2.20, printed p.82.
-/

public section

open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry
open ComponentSelection A5Module
variable {G : Type*} [Group G] [Finite G]
    {K L M V V₁ V₂ : Subgroup G} {T : Sylow 2 G}

/-- Construct the radical, normalizer and split-seed geometry in one chosen
marking. Inputs are the actual doubled module, hypothetical centrality,
and standing, marked local and earlier source conclusions. -/
theorem exists_marked_seed_geometry
    (standing : RankTwo.LocalApplication.SourceHypothesis T L)
    (f : FlagMarking T L V V₁ V₂) (c : LocalConfiguration M f)
    (hM : M = normalizer (L : Set G))
    (e : Thompson.EarlierData K L (T : Subgroup G) (markedZ f.module) (markedV f.module))
    (d0 : DoubledCoordinates K L (T : Subgroup G) (markedZ f.module) (markedV f.module)
      e.selected.1.1 e.normalizeL e.fixSeed)
    (hc : ⁅plusImage K L (T : Subgroup G) (markedZ f.module) (markedV f.module)
        e.normalizeL e.fixSeed K,
      plusImage K L (T : Subgroup G) (markedZ f.module) (markedV f.module)
        e.normalizeL e.fixSeed (Lv L (markedV f.module))⁆ = ⊥) :
    ∃ d : DoubledCoordinates K L (T : Subgroup G) (markedZ f.module) (markedV f.module)
        e.selected.1.1 e.normalizeL e.fixSeed,
      plusImage K L (T : Subgroup G) (markedZ f.module) (markedV f.module)
        e.normalizeL e.fixSeed (elementaryAbelianMaxJ (Tv (T : Subgroup G) (markedV f.module))) =
          BinaryLinearThree.R.map (modelEmbedding d) ∧
      plusImage K L (T : Subgroup G) (markedZ f.module) (markedV f.module)
        e.normalizeL e.fixSeed (ChapterB.baumann (T : Subgroup G)) =
          BinaryLinearThree.R.map (modelEmbedding d) ∧
      (d.actionMap.comp (inclusion
        (show componentNormalizer K (T : Subgroup G) ≤ K from inf_le_left))).range =
          Matrix.PSL3Two.lineParabolicSL ∧
      ∃ x y : BinaryLinearThree.Vector, x 2 = 0 ∧ x ≠ 0 ∧
        ((⁅zpowers (markedZ f.module), Lv L (markedV f.module)⁆ : Subgroup G).subgroupOf
          (UK K L (T : Subgroup G) (markedZ f.module) (markedV f.module))).map
            d.moduleEquiv.toMonoidHom =
              (BinaryLinearThree.DoubledParabolic.splitPlane x y).toAddSubgroup.toSubgroup := by
  obtain ⟨d, hJ, hB⟩ := Thompson.exists_radical_images_of_marked standing f c e d0 hc
  have hN := componentNormalizer_actionMap_range e.selected.1.1 e.normalizeL e.fixSeed
    e.normalizeK d c.reductions.centralizerSylow c.reductions.sylow_image e.baumann_eq hB
  have h1365 := c.reductions.normalizer_baumann
  have hlocal := c.reductions.local_centralizer
  rw [hM] at h1365 hlocal
  let : IsElementaryAbelian 2 (omegaOneCenterAmbient (Qv (markedV f.module))) :=
    omegaOneCenterAmbient_elementaryAbelian _
  let : IsElementaryAbelian 2 (Uv (markedZ f.module) (markedV f.module)) :=
    IsElementaryAbelian.of_le (Uv_le_coreOmega (T : Subgroup G) _ _
      e.tvSylow e.seedOmega e.characteristicTwo)
  obtain ⟨d', ha, hm, x, y, hx, hne, hQ⟩ := SplitSeed.exists_split_seed
    T standing f.module e.selected e.normalizeK e.normalizeL e.fixSeed d
    c.reductions.centralizerSylow c.reductions.sylow_image e.baumann_eq h1365 hlocal hc hJ hB
  have he : modelEmbedding d' = modelEmbedding d := by
    unfold modelEmbedding
    rw [ha]
  exact ⟨d', he.symm ▸ hJ, he.symm ▸ hB, hm.symm ▸ hN, x, y, hx, hne, hQ⟩

/-- The central branch is impossible for an actual doubled-natural marking.
Both geometric inputs of `false_of_marked_seed_geometry` are constructed
above; the normalization premises are precisely the earlier source ones. -/
theorem false_of_marked_doubled
    (standing : RankTwo.LocalApplication.SourceHypothesis T L)
    (f : FlagMarking T L V V₁ V₂) (c : LocalConfiguration M f)
    (hM : M = normalizer (L : Set G))
    (e : Thompson.EarlierData K L (T : Subgroup G) (markedZ f.module) (markedV f.module))
    (d0 : DoubledCoordinates K L (T : Subgroup G) (markedZ f.module) (markedV f.module)
      e.selected.1.1 e.normalizeL e.fixSeed)
    (hc : ⁅plusImage K L (T : Subgroup G) (markedZ f.module) (markedV f.module)
        e.normalizeL e.fixSeed K,
      plusImage K L (T : Subgroup G) (markedZ f.module) (markedV f.module)
        e.normalizeL e.fixSeed (Lv L (markedV f.module))⁆ = ⊥) : False := by
  obtain ⟨d, _, _, hN, x, y, hx, hne, hQ⟩ :=
    exists_marked_seed_geometry standing f c hM e d0 hc
  have h1365 := c.reductions.normalizer_baumann
  have hlocal := c.reductions.local_centralizer
  rw [hM] at h1365 hlocal
  exact false_of_marked_seed_geometry f.module K (T : Subgroup G) e.selected.1.1
    e.normalizeL e.fixSeed d h1365 hlocal hN x y hx hne hQ

/-- Source application with full Hypothesis 13.3.1 and an actual A₅ flag.
Construct the earlier package from 13.6.2–5, the characteristic-two
conclusion, component invariance and 13.6.16(3), then exclude centrality.
The independent B.5 producer supplies the doubled marking d0. -/
theorem false_of_source_doubled
    (standing : RankTwo.LocalApplication.SourceHypothesis T L)
    (f : FlagMarking T L V V₁ V₂) (c : LocalConfiguration M f)
    (hM : M = normalizer (L : Set G))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ f.module) (markedV f.module))
    (hn : Tv (T : Subgroup G) (markedV f.module) ≤ normalizer (K : Set G))
    (hchar : Theory.GroupTheory.generalizedFitting (Gv (markedV f.module)) =
      pCore 2 (Gv (markedV f.module)))
    (hgen : K = ⁅K, elementaryAbelianMaxJ (Tv (T : Subgroup G) (markedV f.module))⁆)
    (d0 : let e := Thompson.FullAction.sourceEarlierData f c hTL hK hn hchar hgen
      DoubledCoordinates K L (T : Subgroup G) (markedZ f.module) (markedV f.module)
        e.selected.1.1 e.normalizeL e.fixSeed)
    (hc : let e := Thompson.FullAction.sourceEarlierData f c hTL hK hn hchar hgen
      ⁅plusImage K L (T : Subgroup G) (markedZ f.module) (markedV f.module)
          e.normalizeL e.fixSeed K,
        plusImage K L (T : Subgroup G) (markedZ f.module) (markedV f.module)
          e.normalizeL e.fixSeed (Lv L (markedV f.module))⁆ = ⊥) : False :=
  false_of_marked_doubled standing f c hM
    (Thompson.FullAction.sourceEarlierData f c hTL hK hn hchar hgen) d0 hc

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry
