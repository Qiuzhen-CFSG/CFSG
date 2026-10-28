module

public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.NormalizerProduct
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.ResidualRank
public import Theory.GroupTheory.IndexThreeResidual

/-!
# The source residual product in the two-core-kernel branch

The already constructed index [H:H∩M]=3 puts O^{2,3}(H) inside H∩M.
Apply the genuine earlier 13.3.9 alternative to this normal two-perfect
subgroup to show that H is a {2,3}-group. The ordinary-row identity
L=O^{3′}(M) from 13.4.2(5) identifies O^{3′}(H∩M) with the literal
L₁=O^{3′}(C_L(z)). The original Sylow subgroup then gives H∩M=L₁T.
Combining this with the constructed Thompson supplement proves H=L₁IT,
both as a subgroup join and as a setwise product.

The final branch theorem also gives the actual S₃ quotient of I, the
rank-two moved plane, three-rank one for L₁, and I≰M. It assumes neither
the product nor the index. The initial 13.4.9 identity M=LT follows from
the same intersection and its earlier centralizer supplement.

The exact earlier 13.3.9 alternative and 13.4.2(5) equality stay explicit;
their earlier-source producers retain discharge with qt-d-1341-fixed-core-source.
Selecting the ordinary row needed for 13.4.2(5), source R₁ placement and
residual order, A₆-block noncentrality, the larger kernel, the S₃×S₃ quotient
and chamber construction remain with qt-d-1341-solvable-source. Thus this
module does not establish full 13.4.8–9.
Source: Aschbacher–Smith 13.3.9, p.887; 13.4.2(5), p.897;
13.4.8–9, pp.905–906.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
variable {G : Type*} [Group G] [Finite G] {L : Subgroup G}

theorem firstCentralizerResidual_eq_intersection_residual (z : G)
    (h1342 : (primeToResidual 3 (normalizer (L : Set G))).map
      (normalizer (L : Set G)).subtype = L) :
    let C := centralizer ({z} : Set G) ⊓ normalizer (L : Set G)
    (primeToResidual 3 C).map C.subtype = firstCentralizerResidual L z := by
  have he := embedded_primeToResidual_intersection_of_le 3 (normalizer (L : Set G)) L
    (centralizer ({z} : Set G) ⊓ normalizer (L : Set G)) inf_le_right h1342
  have hi : L ⊓ (centralizer ({z} : Set G) ⊓ normalizer (L : Set G)) =
      L ⊓ centralizer ({z} : Set G) := by
    apply le_antisymm (inf_le_inf_left L inf_le_left)
    exact le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans L.le_normalizer))
  rw [hi] at he
  rw [firstCentralizerResidual_eq]
  exact he
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable

namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Stellmacher Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem centralizer_twoThree_of_normalizer_index {z : G}
    (hi : (normalizer (L : Set G)).relIndex (centralizer ({z} : Set G)) = 3)
    (h1339 : ∀ Y : Subgroup G, Y ≤ centralizer ({z} : Set G) →
      centralizer ({z} : Set G) ≤ normalizer (Y : Set G) →
      Y ≤ normalizer (L : Set G) → IsPPerfect 2 Y →
      Y = ⊥ ∨ Nat.card (Y ⧸ pCore 2 Y) = 3) :
    IsPiGroup twoThreePrimes (centralizer ({z} : Set G)) := by
  let H := centralizer ({z} : Set G)
  let M := (normalizer (L : Set G)).subgroupOf H
  apply twoThree_of_index_three_normal_twoPerfect M hi
  intro Y hnY hYM hp
  let := hnY
  let A := Y.map H.subtype
  let e : Y ≃* A := Y.equivMapOfInjective H.subtype H.subtype_injective
  have hAH : A ≤ H := map_subtype_le _
  have hnA : H ≤ normalizer (A : Set G) := by
    have hh := (map_mono (show (⊤ : Subgroup H) ≤ normalizer (Y : Set H)
      from le_normalizer_of_normal)).trans (Y.le_normalizer_map H.subtype)
    simpa only [← MonoidHom.range_eq_map, range_subtype] using hh
  have hAM : A ≤ normalizer (L : Set G) := by
    rintro a ⟨y,hy,rfl⟩
    exact hYM hy
  rcases h1339 A hAH hnA hAM (hp.of_surjective e.toMonoidHom e.surjective) with hb | hc
  · exact Or.inl ((Y.map_eq_bot_iff_of_injective H.subtype_injective).mp hb)
  · exact Or.inr ((Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv).trans hc)

theorem centralizer_intersection_product_of_twoThree
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
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
    (h.source_sylow_normalizes structural)
  have hCpi : IsPiGroup twoThreePrimes C :=
    hpi.of_injective (inclusion (show C ≤ H from inf_le_left)) (inclusion_injective _)
  have hs := congrArg (Subgroup.map C.subtype)
    (primeToResidual_three_sup_sylow_of_twoThree hCpi (T.subtype hTC))
  rw [Subgroup.map_sup, h1342, Sylow.coe_subtype,
    map_subgroupOf_eq_of_le hTC, ← MonoidHom.range_eq_map, range_subtype] at hs
  exact hs.symm

theorem centralizer_firstResidual_product_of_normalizer_product
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
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
  rw [hprod, centralizer_intersection_product_of_twoThree h structural hz hpi h1342,
    ← sup_assoc, sup_comm I]

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable

namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Stellmacher Chapter12.Section02 Chapter14.Section03.FaithfulSource
open scoped Pointwise
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem centralizer_single_factor_source_product_of_baumann_bound
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
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
    centralizer_single_factor_normalizer_product_of_baumann_bound h₀ h structural hz hzL f R hR
      hQR hsolv hkernel hB hout hindex horder hthree hAN
  let H := centralizer ({z} : Set G)
  let I := conjugateSpanBy (elementaryAbelianMaxJ R) H
  let A := firstCentralizerResidual L z
  let C := H ⊓ normalizer (L : Set G)
  have hTH : (T : Subgroup G) ≤ H := original_sylow_le_centralizer hz
  have hTC : (T : Subgroup G) ≤ C := le_inf hTH (h.source_sylow_normalizes structural)
  have hAH : A ≤ H := (firstCentralizerResidual_le L z).trans inf_le_right
  obtain ⟨hpi,hgen⟩ := centralizer_firstResidual_product_of_normalizer_product
    h structural hz I hprod hi h1339 hres
  have hinter := centralizer_intersection_product_of_twoThree h structural hz hpi hres
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

omit [Finite G] in
/-- The initial product equality in 13.4.9 follows from the same literal intersection. -/
theorem normalizer_eq_component_sylow_of_centralizer_intersection {z : G}
    (hsupp : normalizer (L : Set G) =
      L ⊔ (centralizer ({z} : Set G) ⊓ normalizer (L : Set G)))
    (hinter : centralizer ({z} : Set G) ⊓ normalizer (L : Set G) =
      firstCentralizerResidual L z ⊔ (T : Subgroup G)) :
    normalizer (L : Set G) = L ⊔ (T : Subgroup G) := by
  rw [hsupp, hinter, ← sup_assoc, sup_eq_left.mpr ((firstCentralizerResidual_le L z).trans inf_le_left)]

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
