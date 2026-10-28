module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SolvableAt.LocalProduct.NormalizerProduct
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SolvableAt.LocalProduct.SourceProduct
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.ShortBlock

public import Theory.Representation.BinaryPermutation.SixCoreCentralKernel
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.BlockContainment

/-!
# The short-block branch of the solvable centralizer product: structure at the original group

Specialize the original proof to `Structural1222At` at the same G,T.
All action maps, full quotient kernels and source hypotheses are retained;
no universal Chapter12 record is inferred. Intrinsic model and group lemmas
are reused from the preserved source module. This family feeds guarded
solvable-centralizer recognition on the actual five-dimensional module.

Source: Aschbacher--Smith 13.4.8--9, printed pp.904--907;
see the original `Solvable/LocalProduct/ShortBlock` proof for the local step.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Subgroup Theory.GroupTheory
open Chapter12.Section02 Stellmacher Chapter14.Section03.FaithfulSource
open Section08.TransvectionRecognition.Component.ModelExtension
open scoped Pointwise
universe u

/-- The short-block product and intersection with the actual normalizer. -/
theorem centralizer_pair_quotient_of_short_block_at
    {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D) (hb : ChapterC.IsShort L)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (R : Subgroup G) (hRT : R ≤ T)
    (hnR : (T : Subgroup G) ≤ normalizer (R : Set G))
    (hQR : (centralizer ({z.val} : Set G)).pCoreIn 2 ≤ R)
    (hVJ : V ≤ elementaryAbelianMaxJ R)
    (hsolv : Group.IsSolvable (centralizer ({z.val} : Set G)))
    (hkernel : centralizer ((centralizerOmegaOrbit T z.val).subgroupOf
      (centralizer ({z.val} : Set G)) : Set (centralizer ({z.val} : Set G))) =
      pCore 2 (centralizer ({z.val} : Set G)))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hAN : firstCentralizerResidual L z.val ≤ normalizer (R : Set G))
    (h1339 : ∀ Y : Subgroup G, Y ≤ centralizer ({z.val} : Set G) →
      centralizer ({z.val} : Set G) ≤ normalizer (Y : Set G) →
      Y ≤ normalizer (L : Set G) → IsPPerfect 2 Y →
      Y = ⊥ ∨ Nat.card (Y ⧸ pCore 2 Y) = 3)
    (h1342 : (primeToResidual 3 (normalizer (L : Set G))).map
      (normalizer (L : Set G)).subtype = L) :
    let H := centralizer ({z.val} : Set G)
    let I := conjugateSpanBy (elementaryAbelianMaxJ R) H
    Nonempty ((H ⧸ pCore 2 H) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∧
      Nonempty ((I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 3)) ∧
      Representation.BinaryOffender.rank (⁅centralizerOmegaOrbit T z.val,I⁆ : Subgroup G) = 2 ∧
      H = firstCentralizerResidual L z.val ⊔ I ⊔ (T : Subgroup G) ∧
      H ⊓ normalizer (L : Set G) = firstCentralizerResidual L z.val ⊔ (T : Subgroup G) ∧
      (H : Set G) = (firstCentralizerResidual L z.val : Set G) * (I : Set G) * (T : Set G) := by
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  have hJ := centralizer_thompson_noncentral_of_short_block h₀ D m hb
    z hz hzL hsolv R hVJ hkernel
  obtain ⟨eo⟩ := ordinary_of_short_core_marking D m hb
  have hcore : IsPGroup 2 (centralCore L) := by
    rw [centralCore_eq_twoCore_of_ordinary eo]
    exact pCore_isPGroup
  obtain ⟨ho,hthree⟩ := firstCentralizerResidual_order_of_core_marking D m hcore z hzL
  have hm := centralizer_thompson_single_factor_of_twoCore_kernel h₀ hz hz1 R hRT hnR hQR hJ
    hsolv hkernel (firstCentralizerResidual L z.val)
    ((firstCentralizerResidual_le L z.val).trans inf_le_right)
    (firstCentralizerResidual_twoPerfect L z.val) ho hAN
    (firstCentralizerResidual_noncentral_of_twoCore_kernel hkernel hthree)
  have hprod := centralizer_thompson_normalizer_product_at h₀ h structural hz hzL R hRT hQR hJ
    hsolv hindex hm
  obtain ⟨hq,hr⟩ := centralizer_thompson_single_factor_data_of_firstResidual h₀ hz hz1
    R hRT hnR hQR hJ hsolv hkernel ho hthree hAN
  have hi := centralizer_thompson_normalizer_index_at h structural hz R hRT hq hprod hout
  have hres := firstCentralizerResidual_eq_intersection_residual z.val h1342
  let H := centralizer ({z.val} : Set G)
  let I := conjugateSpanBy (elementaryAbelianMaxJ R) H
  let A := firstCentralizerResidual L z.val
  obtain ⟨hpi,hgen⟩ := centralizer_firstResidual_product_of_normalizer_product_at
    h structural hz I hprod hi h1339 hres
  have hinter := centralizer_intersection_product_of_twoThree_at h structural hz hpi hres
  refine ⟨centralizer_pair_quotient_of_source_product D m hcore z hzL hz R hRT
    hq hgen hinter hout,hq,hr,hgen,hinter,?_⟩
  have hTH : (T : Subgroup G) ≤ H := original_sylow_le_centralizer hz
  have hAH : A ≤ H := (firstCentralizerResidual_le L z.val).trans inf_le_right
  have hnA : (T : Subgroup G) ≤ normalizer (A : Set G) := by
    rw [show A = firstCentralizerResidual L z.val from rfl,firstCentralizerResidual_eq]
    have hn : (T : Subgroup G) ≤ normalizer
        ((L ⊓ H : Subgroup G) : Set G) :=
      (le_inf D.sylow_normalizes_component (hTH.trans H.le_normalizer)).trans
        inf_normalizer_le_normalizer_inf
    exact hn.trans (normalizer_le_normalizer_characteristic_image _ (primeToResidual 3 _))
  have hnI : H ≤ normalizer (I : Set G) := le_normalizer_conjugateSpanBy _ _
  have hnAI : (T : Subgroup G) ≤ normalizer ((A ⊔ I : Subgroup G) : Set G) :=
    (le_inf hnA (hTH.trans hnI)).trans (normalizer_inf_normalizer_le_normalizer_sup A I)
  calc
    (H : Set G) = ((A ⊔ I ⊔ (T : Subgroup G) : Subgroup G) : Set G) :=
      congrArg (fun B : Subgroup G => (B : Set G)) hgen
    _ = ((A ⊔ I : Subgroup G) : Set G) * (T : Set G) :=
      coe_mul_of_right_le_normalizer_left _ _ hnAI
    _ = (A : Set G) * (I : Set G) * (T : Set G) := by
      rw [coe_mul_of_left_le_normalizer_right A I (hAH.trans hnI)]

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
