module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.Thompson.FullAction.Faithfulness
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo.LocalApplication.SourceInputs
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration

/-!
# The full doubled action in the actual marked source configuration

The local A₅ configuration supplies the actual centralizer Sylow, the cubic
residual quotient and 13.6.4. The Sylow-central marking and the genuine earlier
13.6.6, 13.6.14 and 13.6.16(3) conclusions construct `EarlierData` on these
same subgroups. The proved 13.6.11 application supplies [U_K,L_v] ≠ 1.

Under hypothetical centrality, the full conjugation action in any supplied
doubled marking is faithful and normalizes the diagonal component. Every
field of `ExtendedCoordinates` is constructed. Full Hypothesis 13.3.1,
with KnownSimple and the uniform A₅ choice, is retained by the source theorem.
The genuine earlier-source premises remain with their section owners; this
module assumes no later containment, radical equality or parabolic image.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.6.2–16 and the proof of 13.6.20, printed pp.926–931.
-/

@[expose] public section
open Subgroup Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.Thompson.FullAction
open ComponentSelection A5Module
variable {G : Type*} [Group G] [Finite G]
    {K L M V V₁ V₂ : Subgroup G} {T : Sylow 2 G}

/-- The earlier source package on the literal marked local subgroups.
The remaining inputs are the earlier normalization, characteristic-two,
13.6.14 invariance and 13.6.16(3) conclusions. -/
theorem sourceEarlierData (f : FlagMarking T L V V₁ V₂)
    (c : LocalConfiguration M f)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ f.module) (markedV f.module))
    (hn : Tv (T : Subgroup G) (markedV f.module) ≤ normalizer (K : Set G))
    (hchar : Theory.GroupTheory.generalizedFitting (Gv (markedV f.module)) =
      pCore 2 (Gv (markedV f.module)))
    (hgen : K = ⁅K, elementaryAbelianMaxJ (Tv (T : Subgroup G) (markedV f.module))⁆) :
    EarlierData K L (T : Subgroup G) (markedZ f.module) (markedV f.module) where
  selected := hK
  tvSylow := ⟨c.reductions.centralizerSylow, c.reductions.sylow_image⟩
  normalizeL := normalizes_Lv_of_normalizes_L _ L _ (inf_le_left.trans hTL) inf_le_right
  fixSeed := by
    intro t ht
    exact mem_centralizer_singleton_iff.mpr
      (((mem_omegaOneCenterAmbient_iff _ _).mp f.z_central).2.2 t ht.1)
  normalizeK := hn
  seedOmega := by
    have hz := (mem_omegaOneCenterAmbient_iff (T : Subgroup G) _).mp f.z_central
    exact (mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨⟨hz.1, markedZ_mem_Gv f.module⟩, hz.2.1, fun t ht => hz.2.2 t ht.1⟩
  characteristicTwo := hchar
  baumann_eq := c.reductions.baumann_eq
  component_generated := hgen

/-- Apply the construction to any earlier source package on the actual flag.
The genuine cubic quotient and nontrivial commutator are discharged here. -/
theorem exists_extendedCoordinates_of_marked
    (_standing : RankTwo.LocalApplication.SourceHypothesis T L)
    (f : FlagMarking T L V V₁ V₂) (c : LocalConfiguration M f)
    (e : EarlierData K L (T : Subgroup G) (markedZ f.module) (markedV f.module))
    (d0 : DoubledCoordinates K L (T : Subgroup G) (markedZ f.module) (markedV f.module)
      e.selected.1.1 e.normalizeL e.fixSeed)
    (hc : ⁅plusImage K L (T : Subgroup G) (markedZ f.module) (markedV f.module)
        e.normalizeL e.fixSeed K,
      plusImage K L (T : Subgroup G) (markedZ f.module) (markedV f.module)
        e.normalizeL e.fixSeed (Lv L (markedV f.module))⁆ = ⊥) :
    Nonempty (ExtendedCoordinates e d0) := by
  let : IsElementaryAbelian 2 (omegaOneCenterAmbient (Qv (markedV f.module))) :=
    omegaOneCenterAmbient_elementaryAbelian _
  let : IsElementaryAbelian 2 (Uv (markedZ f.module) (markedV f.module)) :=
    IsElementaryAbelian.of_le (Uv_le_coreOmega (T : Subgroup G) _ _
      e.tvSylow e.seedOmega e.characteristicTwo)
  have hne := UK_commutator_ne_bot f.module K (T : Subgroup G)
    c.reductions.centralizerSylow c.reductions.sylow_image e.fixSeed e.selected e.normalizeK
  exact ⟨extendedCoordinates e d0 hc c.residual_card hne⟩

/-- Source application retaining full Hypothesis 13.3.1 and constructing the
earlier package from the marked configuration before extending d0. -/
theorem exists_extendedCoordinates_of_source
    (standing : RankTwo.LocalApplication.SourceHypothesis T L)
    (f : FlagMarking T L V V₁ V₂) (c : LocalConfiguration M f)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ f.module) (markedV f.module))
    (hn : Tv (T : Subgroup G) (markedV f.module) ≤ normalizer (K : Set G))
    (hchar : Theory.GroupTheory.generalizedFitting (Gv (markedV f.module)) =
      pCore 2 (Gv (markedV f.module)))
    (hgen : K = ⁅K, elementaryAbelianMaxJ (Tv (T : Subgroup G) (markedV f.module))⁆)
    (d0 : let e := sourceEarlierData f c hTL hK hn hchar hgen
      DoubledCoordinates K L (T : Subgroup G) (markedZ f.module) (markedV f.module)
        e.selected.1.1 e.normalizeL e.fixSeed)
    (hc : let e := sourceEarlierData f c hTL hK hn hchar hgen
      ⁅plusImage K L (T : Subgroup G) (markedZ f.module) (markedV f.module)
          e.normalizeL e.fixSeed K,
        plusImage K L (T : Subgroup G) (markedZ f.module) (markedV f.module)
          e.normalizeL e.fixSeed (Lv L (markedV f.module))⁆ = ⊥) :
    Nonempty (ExtendedCoordinates (sourceEarlierData f c hTL hK hn hchar hgen) d0) :=
  exists_extendedCoordinates_of_marked standing f c
    (sourceEarlierData f c hTL hK hn hchar hgen) d0 hc

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.Thompson.FullAction
