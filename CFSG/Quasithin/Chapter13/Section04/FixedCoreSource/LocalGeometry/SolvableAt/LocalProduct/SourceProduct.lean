module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SolvableAt.LocalProduct.NormalizerProduct
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.SourceProduct

public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.NormalizerProduct
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.ResidualRank
public import Theory.GroupTheory.IndexThreeResidual

/-!
# The source residual product in the two-core-kernel branch: structure at the original group

Specialize the original proof to `Structural1222At` at the same G,T.
All action maps, full quotient kernels and source hypotheses are retained;
no universal Chapter12 record is inferred. Intrinsic model and group lemmas
are reused from the preserved source module. This family feeds guarded
solvable-centralizer recognition on the actual five-dimensional module.

Source: Aschbacher--Smith 13.4.8--9, printed pp.904--907;
see the original `Solvable/LocalProduct/SourceProduct` proof for the local step.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
variable {G : Type*} [Group G] [Finite G] {L : Subgroup G}

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable

namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Stellmacher Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem centralizer_intersection_product_of_twoThree_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    {z : G} (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hpi : IsPiGroup twoThreePrimes (centralizer ({z} : Set G)))
    (h1342 :
      let C := centralizer ({z} : Set G) ⊓ normalizer (L : Set G)
      (primeToResidual 3 C).map C.subtype = firstCentralizerResidual L z) :
    centralizer ({z} : Set G) ⊓ normalizer (L : Set G) =
      firstCentralizerResidual L z ⊔ (T : Subgroup G) := by
  let H := centralizer ({z} : Set G)
  let C := H ⊓ normalizer (L : Set G)
  have hTC : (T : Subgroup G) ≤ C := le_inf (original_sylow_le_centralizer hz)
    (h.source_sylow_normalizes_at structural)
  have hCpi : IsPiGroup twoThreePrimes C :=
    hpi.of_injective (inclusion (show C ≤ H from inf_le_left)) (inclusion_injective _)
  have hs := congrArg (Subgroup.map C.subtype)
    (primeToResidual_three_sup_sylow_of_twoThree hCpi (T.subtype hTC))
  rw [Subgroup.map_sup, h1342, Sylow.coe_subtype,
    map_subgroupOf_eq_of_le hTC, ← MonoidHom.range_eq_map, range_subtype] at hs
  exact hs.symm

theorem centralizer_firstResidual_product_of_normalizer_product_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    {z : G} (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G))
    (I : Subgroup G)
    (hprod : centralizer ({z} : Set G) = I ⊔
      (centralizer ({z} : Set G) ⊓ normalizer (L : Set G)))
    (hi : (normalizer (L : Set G)).relIndex (centralizer ({z} : Set G)) = 3)
    (h1339 : ∀ Y : Subgroup G, Y ≤ centralizer ({z} : Set G) →
      centralizer ({z} : Set G) ≤ normalizer (Y : Set G) →
      Y ≤ normalizer (L : Set G) → IsPPerfect 2 Y →
      Y = ⊥ ∨ Nat.card (Y ⧸ pCore 2 Y) = 3)
    (h1342 :
      let C := centralizer ({z} : Set G) ⊓ normalizer (L : Set G)
      (primeToResidual 3 C).map C.subtype = firstCentralizerResidual L z) :
    IsPiGroup twoThreePrimes (centralizer ({z} : Set G)) ∧
      centralizer ({z} : Set G) = firstCentralizerResidual L z ⊔ I ⊔ (T : Subgroup G) := by
  have hpi := centralizer_twoThree_of_normalizer_index hi h1339
  refine ⟨hpi, ?_⟩
  rw [hprod, centralizer_intersection_product_of_twoThree_at h structural hz hpi h1342,
    ← sup_assoc, sup_comm I]

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable

namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Stellmacher Chapter12.Section02 Chapter14.Section03.FaithfulSource
open scoped Pointwise
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem centralizer_single_factor_source_product_of_baumann_bound_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    {z : G} (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z ∉ centralizer (L : Set G))
    {K : Type*} [Group K] (f : T →* K) (R : Subgroup G)
    (hR : R = ((pCore 2 K).comap f).map (T : Subgroup G).subtype)
    (hQR : (centralizer ({z} : Set G)).pCoreIn 2 ≤ R)
    (hsolv : Group.IsSolvable (centralizer ({z} : Set G)))
    (hkernel : centralizer ((centralizerOmegaOrbit T z).subgroupOf
      (centralizer ({z} : Set G)) : Set (centralizer ({z} : Set G))) =
      pCore 2 (centralizer ({z} : Set G)))
    (hB : normalizer (ChapterB.baumann R : Set G) ≤ normalizer (L : Set G))
    (hout : ¬ centralizer ({z} : Set G) ≤ normalizer (L : Set G))
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (horder : ∃ m n : ℕ, Nat.card (firstCentralizerResidual L z) ∣ 2 ^ m * 3 ^ n)
    (hthree : 3 ∣ Nat.card (firstCentralizerResidual L z))
    (hAN : firstCentralizerResidual L z ≤ normalizer (R : Set G))
    (h1339 : ∀ Y : Subgroup G, Y ≤ centralizer ({z} : Set G) →
      centralizer ({z} : Set G) ≤ normalizer (Y : Set G) →
      Y ≤ normalizer (L : Set G) → IsPPerfect 2 Y →
      Y = ⊥ ∨ Nat.card (Y ⧸ pCore 2 Y) = 3)
    (h1342 : (primeToResidual 3 (normalizer (L : Set G))).map
      (normalizer (L : Set G)).subtype = L) :
    let H := centralizer ({z} : Set G)
    let I := conjugateSpanBy (elementaryAbelianMaxJ R) H
    IsPiGroup twoThreePrimes H ∧
      primeRank 3 (firstCentralizerResidual L z) = 1 ∧
      Nonempty ((I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 3)) ∧
      Representation.BinaryOffender.rank (⁅centralizerOmegaOrbit T z,I⁆ : Subgroup G) = 2 ∧
      H = firstCentralizerResidual L z ⊔ I ⊔ (T : Subgroup G) ∧
      H ⊓ normalizer (L : Set G) = firstCentralizerResidual L z ⊔ (T : Subgroup G) ∧
      ¬ I ≤ normalizer (L : Set G) ∧
      (H : Set G) = (firstCentralizerResidual L z : Set G) * (I : Set G) * (T : Set G) := by
  have hres := firstCentralizerResidual_eq_intersection_residual z h1342
  obtain ⟨hq,hr,hprod,hI,hi,_⟩ :=
    centralizer_single_factor_normalizer_product_of_baumann_bound_at h₀ h structural hz hzL f R hR
      hQR hsolv hkernel hB hout hindex horder hthree hAN
  let H := centralizer ({z} : Set G)
  let I := conjugateSpanBy (elementaryAbelianMaxJ R) H
  let A := firstCentralizerResidual L z
  let C := H ⊓ normalizer (L : Set G)
  have hTH : (T : Subgroup G) ≤ H := original_sylow_le_centralizer hz
  have hTC : (T : Subgroup G) ≤ C := le_inf hTH (h.source_sylow_normalizes_at structural)
  have hAH : A ≤ H := (firstCentralizerResidual_le L z).trans inf_le_right
  obtain ⟨hpi,hgen⟩ := centralizer_firstResidual_product_of_normalizer_product_at
    h structural hz I hprod hi h1339 hres
  have hinter := centralizer_intersection_product_of_twoThree_at h structural hz hpi hres
  have hrank := centralizer_firstResidual_threeRank_of_baumann_bound h₀ hz
    (fun he => hzL (he ▸ one_mem _)) f R hR hQR hsolv hkernel hB hout horder hthree hAN
  refine ⟨hpi,hrank,hq,hr,hgen,hinter,hI,?_⟩
  have hnA : (T : Subgroup G) ≤ normalizer (A : Set G) := by
    change (T : Subgroup G) ≤ normalizer (firstCentralizerResidual L z : Set G)
    rw [← hres]
    have hh := (map_mono (show (⊤ : Subgroup C) ≤ normalizer (primeToResidual 3 C : Set C)
      from le_normalizer_of_normal)).trans ((primeToResidual 3 C).le_normalizer_map C.subtype)
    have hnC : C ≤ normalizer ((primeToResidual 3 C).map C.subtype : Set G) := by
      simpa only [← MonoidHom.range_eq_map,range_subtype] using hh
    exact hTC.trans hnC
  have hnI : H ≤ normalizer (I : Set G) := le_normalizer_conjugateSpanBy _ _
  have hnAI : (T : Subgroup G) ≤ normalizer ((A ⊔ I : Subgroup G) : Set G) :=
    (le_inf hnA (hTH.trans hnI)).trans (normalizer_inf_normalizer_le_normalizer_sup A I)
  calc
    (H : Set G) = ((A ⊔ I ⊔ (T : Subgroup G) : Subgroup G) : Set G) := congrArg (fun B : Subgroup G => (B : Set G)) hgen
    _ = ((A ⊔ I : Subgroup G) : Set G) * (T : Set G) := coe_mul_of_right_le_normalizer_left _ _ hnAI
    _ = (A : Set G) * (I : Set G) * (T : Set G) := by
      rw [coe_mul_of_left_le_normalizer_right A I (hAH.trans hnI)]

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
