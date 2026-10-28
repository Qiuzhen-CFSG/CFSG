module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SolvableAt.LocalProduct.ShortConjugates
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.ShortLayerComparison
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.ShortConjugates
public import Theory.Representation.BinaryPermutation.SixCoreQuadraticResidual
/-!
# Comparison of the two original residual layers: structure at the original group

Specialize the original proof to `Structural1222At` at the same G,T.
All action maps, full quotient kernels and source hypotheses are retained;
no universal Chapter12 record is inferred. Intrinsic model and group lemmas
are reused from the preserved source module. This family feeds guarded
solvable-centralizer recognition on the actual five-dimensional module.

Source: Aschbacher--Smith 13.4.8--9, printed pp.904--907;
see the original `Solvable/LocalProduct/ShortLayerComparison` proof for the local step.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02 Stellmacher Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- In the actual larger-kernel short-block contradiction, the moving pair
shares the original residual layer. That layer lies in the intersection
and is centralized by the second five-space. -/
theorem centralizer_larger_short_block_equal_layers_at
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
    (hJ : elementaryAbelianMaxJ R ≤ centralizer (centralizerOmegaOrbit T z.val : Set G))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
    (h1339 : ∀ Y : Subgroup G, Y ≤ centralizer ({z.val} : Set G) →
      centralizer ({z.val} : Set G) ≤ normalizer (Y : Set G) →
      Y ≤ normalizer (L : Set G) → IsPPerfect 2 Y →
      Y = ⊥ ∨ (Y = selectedFirstResidual T L V z.val ∧ Nat.card (Y ⧸ pCore 2 Y) = 3)) :
    let H := centralizer ({z.val} : Set G)
    let W := ⁅V,firstCentralizerResidual L z.val⁆
    ∃ g ∈ H,
      V.conjBy g ≤ H.pCoreIn 2 ∧
      W.conjBy g = W ∧
      W ≤ V ⊓ V.conjBy g ∧
      V.conjBy g ≤ centralizer (W : Set G) ∧
      ⁅V,V.conjBy g⁆ ≤ V ⊓ V.conjBy g ∧
      ⁅V,V.conjBy g⁆ ≠ ⊥ ∧
      ¬ V ⊓ centralizer (L : Set G) ≤ V.conjBy g := by
  obtain ⟨hn,g,hg,hgQ,hnQ,hcomm,hne,hfixed,_⟩ :=
    centralizer_larger_short_block_moving_layers_at h₀ h structural D m hb z hz hzL
      hlarge R hRT S hR hVJ hJ hout hfusion h1339
  obtain ⟨hc,_,_,_⟩ := centralizer_larger_kernel_local_data h₀ hz
    (fun he => hzL (he ▸ one_mem _)) R hRT S hR
  have hVQ : V ≤ (centralizer ({z.val} : Set G)).pCoreIn 2 := by
    rw [← hc]
    exact le_inf (hVJ.trans (sSup_le fun _ hA => hA.1)) (hVJ.trans hJ)
  have he := centralizer_short_block_conjugate_residual_layer_eq
    D m hb z hz hzL hVQ hn g hg hnQ
  have hWV : ⁅V,firstCentralizerResidual L z.val⁆ ≤ V :=
    le_normalizer_iff_commutator_le_left.mp
      (((firstCentralizerResidual_le L z.val).trans inf_le_left).trans D.normalizes)
  have hWVg : ⁅V,firstCentralizerResidual L z.val⁆ ≤ V.conjBy g := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hWV
    change (⁅V,firstCentralizerResidual L z.val⁆).conjBy g ≤ V.conjBy g at hh
    rwa [he] at hh
  let := D.elementary
  let : IsMulCommutative (V.conjBy g) :=
    inferInstanceAs (IsMulCommutative (V.map (MulAut.conj g).toMonoidHom))
  have hcVg : V.conjBy g ≤ centralizer (V.conjBy g : Set G) :=
    le_centralizer_iff_isMulCommutative.mpr inferInstance
  exact ⟨g,hg,hgQ,he,le_inf hWV hWVg,
    hcVg.trans (centralizer_le hWVg),hcomm,hne,hfixed⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
