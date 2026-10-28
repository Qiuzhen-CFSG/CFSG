module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NormalizerAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SolvableAt.LocalProduct.ShortLayerComparison
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.ShortLayerFixedLine
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.ShortLayerComparison
public import Theory.Representation.BinaryPermutation.SixCoreFixedLayer
/-!
# The fixed-line contradiction for the larger kernel: structure at the original group

Specialize the original proof to `Structural1222At` at the same G,T.
All action maps, full quotient kernels and source hypotheses are retained;
no universal Chapter12 record is inferred. Intrinsic model and group lemmas
are reused from the preserved source module. This family feeds guarded
solvable-centralizer recognition on the actual five-dimensional module.

Source: Aschbacher--Smith 13.4.8--9, printed pp.904--907;
see the original `Solvable/LocalProduct/ShortLayerFixedLine` proof for the local step.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02 Stellmacher Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The moving-layer comparison and fixed-line orbit calculation discharge
the centralizing Thompson alternative in the actual larger-kernel short-block
branch. Earlier residual classification, fusion and Sylow placement are the
only remaining earlier-source inputs. -/
theorem centralizer_larger_thompson_noncentral_of_short_block_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D) (hb : ChapterC.IsShort L)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hlarge : centralizer ((centralizerOmegaOrbit T z.val).subgroupOf
      (centralizer ({z.val} : Set G)) : Set (centralizer ({z.val} : Set G))) ≠
      pCore 2 (centralizer ({z.val} : Set G)))
    (R : Subgroup G) (hRT : R ≤ T)
    (S : Sylow 2 (residualSectionCentralizer 2
      (centralizer ((centralizerOmegaOrbit T z.val).subgroupOf
        (centralizer ({z.val} : Set G)) : Set (centralizer ({z.val} : Set G))))))
    (hR : ((S : Subgroup _).map (residualSectionCentralizer 2
      (centralizer ((centralizerOmegaOrbit T z.val).subgroupOf
        (centralizer ({z.val} : Set G)) : Set (centralizer ({z.val} : Set G))))).subtype).map
          (centralizer ({z.val} : Set G)).subtype = R)
    (hVJ : V ≤ elementaryAbelianMaxJ R)
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
    (h1339 : ∀ Y : Subgroup G, Y ≤ centralizer ({z.val} : Set G) →
      centralizer ({z.val} : Set G) ≤ normalizer (Y : Set G) →
      Y ≤ normalizer (L : Set G) → IsPPerfect 2 Y →
      Y = ⊥ ∨ (Y = selectedFirstResidual T L V z.val ∧ Nat.card (Y ⧸ pCore 2 Y) = 3)) :
    ¬ elementaryAbelianMaxJ R ≤ centralizer (centralizerOmegaOrbit T z.val : Set G) := by
  classical
  intro hJ
  obtain ⟨g,hg,hgQ,_,hWN,hW,hcomm,hne,hfixed⟩ :=
    centralizer_larger_short_block_equal_layers_at h₀ h structural D m hb z hz hzL
      hlarge R hRT S hR hVJ hJ hout hfusion h1339
  have hn : ∃ n ∈ V.conjBy g, n ∉ centralizer (V : Set G) := by
    by_contra! hall
    exact hne (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hall))
  obtain ⟨n,hn,hnc⟩ := hn
  have hTH : (T : Subgroup G) ≤ centralizer ({z.val} : Set G) :=
    original_sylow_le_centralizer hz
  have hQT : (centralizer ({z.val} : Set G)).pCoreIn 2 ≤ T := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH] using
      pCoreIn_le_sylow _ (T.subtype hTH)
  have hnL := D.sylow_normalizes_component (hQT (hgQ hn))
  have hnV := normalizer_component_le_module_at h structural D m hnL
  have hline := fixed_le_of_centralizing_residual_layer D m z hzL
    (V ⊓ V.conjBy g) hWN n hnV hnL (hW hn) hnc (by
      intro v
      apply hcomm
      rw [commutator_comm]
      exact commutator_mem_commutator hn v.property)
  exact hfixed (hline.trans inf_le_right)

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
