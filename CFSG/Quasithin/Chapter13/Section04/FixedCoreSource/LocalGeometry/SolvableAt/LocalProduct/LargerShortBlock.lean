module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SolvableAt.LocalProduct.NormalizerProduct
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SolvableAt.LocalProduct.ShortConjugates
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SolvableAt.LocalProduct.ShortLayerFixedLine
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SolvableAt.LocalProduct.SourceProduct
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.LargerShortBlock
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.ShortLayerFixedLine

/-!
# The larger-kernel short-block local product: structure at the original group

Specialize the original proof to `Structural1222At` at the same G,T.
All action maps, full quotient kernels and source hypotheses are retained;
no universal Chapter12 record is inferred. Intrinsic model and group lemmas
are reused from the preserved source module. This family feeds guarded
solvable-centralizer recognition on the actual five-dimensional module.

Source: Aschbacher--Smith 13.4.8--9, printed pp.904--907;
see the original `Solvable/LocalProduct/LargerShortBlock` proof for the local step.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section08.TransvectionRecognition.Component.ModelExtension
open scoped Pointwise
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The larger-kernel short-block branch supplies the actual S₃×S₃ quotient,
local product, moved plane and unique outside parabolic, using the proved
moving-layer contradiction instead of a Baumann-normalizer bound. -/
theorem centralizer_pair_quotient_of_larger_short_block_at
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
      Y = ⊥ ∨ (Y = selectedFirstResidual T L V z.val ∧ Nat.card (Y ⧸ pCore 2 Y) = 3))
    (hsolv : Group.IsSolvable (centralizer ({z.val} : Set G)))
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (h1342 : (primeToResidual 3 (normalizer (L : Set G))).map
      (normalizer (L : Set G)).subtype = L) :
    let H := centralizer ({z.val} : Set G)
    let I := conjugateSpanBy (elementaryAbelianMaxJ R) H
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
      Nonempty ((H ⧸ pCore 2 H) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∧
      Nonempty ((I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 3)) ∧
      Representation.BinaryOffender.rank (⁅centralizerOmegaOrbit T z.val,I⁆ : Subgroup G) = 2 ∧
      H = firstCentralizerResidual L z.val ⊔ I ⊔ (T : Subgroup G) ∧
      H ⊓ normalizer (L : Set G) = firstCentralizerResidual L z.val ⊔ (T : Subgroup G) ∧
      (H : Set G) = (firstCentralizerResidual L z.val : Set G) * (I : Set G) * (T : Set G) ∧
      I ⊔ (T : Subgroup G) ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      ∀ Y : Subgroup G, Y ≤ H →
        (Y ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ↔
          Y = I ⊔ (T : Subgroup G)) := by
  have ordinary := ordinary_of_short_core_marking D m hb
  have hres := (centralizer_short_block_residual_normal_of_source1339_at
    h₀ h structural D m hb z hz hzL hlarge h1339).1
  have hJ := centralizer_larger_thompson_noncentral_of_short_block_at
    h₀ h structural D m hb z hz hzL hlarge R hRT S hR hVJ hout hfusion h1339
  have h1339' : ∀ Y : Subgroup G, Y ≤ centralizer ({z.val} : Set G) →
      centralizer ({z.val} : Set G) ≤ normalizer (Y : Set G) →
      Y ≤ normalizer (L : Set G) → IsPPerfect 2 Y →
      Y = ⊥ ∨ Nat.card (Y ⧸ pCore 2 Y) = 3 := by
    intro Y hYH hn hYM hp
    exact (h1339 Y hYH hn hYM hp).imp_right (fun hh => hh.2)
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  refine ⟨ordinary,?_⟩
  obtain ⟨eo⟩ := ordinary
  have hcore : IsPGroup 2 (centralCore L) := by
    rw [centralCore_eq_twoCore_of_ordinary eo]
    exact pCore_isPGroup
  have hcard := centralizer_kernel_residual_core_card_of_firstResidual D m hcore z hzL hres
  obtain ⟨hc,_,_,_⟩ := centralizer_larger_kernel_local_data h₀ hz hz1 R hRT S hR
  have hQR := hc.symm.le.trans inf_le_left
  obtain ⟨hq,hm⟩ := centralizer_single_factor_of_cubic_residual_section h₀ hz hz1
    R hRT S hR hcard hJ hsolv
  have hfour := centralizer_thompson_commutator_card_of_single_factor h₀ hz hz1 R hRT
    hQR hJ hsolv hm
  have hr : Representation.BinaryOffender.rank (⁅centralizerOmegaOrbit T z.val,
      conjugateSpanBy (elementaryAbelianMaxJ R) (centralizer ({z.val} : Set G))⁆ : Subgroup G) = 2 := by
    change Nat.log 2 _ = 2
    rw [hfour]
    decide
  have hprod := centralizer_thompson_normalizer_product_at h₀ h structural hz hzL R hRT hQR hJ
    hsolv hindex hm
  have hi := centralizer_thompson_normalizer_index_at h structural hz R hRT hq hprod hout
  have hres := firstCentralizerResidual_eq_intersection_residual z.val h1342
  let H := centralizer ({z.val} : Set G)
  let I := conjugateSpanBy (elementaryAbelianMaxJ R) H
  let A := firstCentralizerResidual L z.val
  obtain ⟨hpi,hgen⟩ := centralizer_firstResidual_product_of_normalizer_product_at
    h structural hz I hprod hi h1339' hres
  have hinter := centralizer_intersection_product_of_twoThree_at h structural hz hpi hres
  have hu := centralizer_thompson_unique_of_source_product D m hcore z hzL hz
    R hRT hq hgen hinter hout
  refine ⟨centralizer_pair_quotient_of_source_product D m hcore z hzL hz R hRT
    hq hgen hinter hout,hq,hr,hgen,hinter,?_,hu⟩
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
