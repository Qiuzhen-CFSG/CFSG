module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.ThompsonNormalizer
public import Theory.GroupTheory.SymmetricThreeFactorSelection
public import Theory.GroupTheory.PResidual.PrimeToPerfect
public import Theory.Quasithin.Rank

/-!
# A single Thompson factor in the two-core-kernel case

Work in the literal H=C_G(z), with V_H=⟨Ω₁(Z(T))^H⟩. In case (i) of
13.4.4(2), C_H(V_H)=O₂(H), so the original three-rank bound passes to
this quotient. The Thompson image is a marked Sylow subgroup of its
normal span. A nontrivial two-perfect {2,3}-actor normalizing it excludes
the two-factor alternative. Restricting the quotient to the original
span then identifies its kernel with that span's two-core.

The final application uses the actual L₁=O^{3′}(C_L(z)), not O³ or a
model tag. Its definition gives two-perfectness, and its cubic divisor
forces nontrivial action through the two-group kernel. This establishes
the S₃ quotient clause for this source branch; it does not yet construct
the full product H=L₁IT or settle the larger-centralizer-kernel case.
The source R₁ placement, Thompson noncentrality, local residual order
and normalization remain obligations of qt-d-1341-solvable-source.
Earlier 13.4.4 inputs retain final discharge with qt-d-1341-fixed-core-source.

Source: Aschbacher–Smith, 13.4.8, printed pp.904–905.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Stellmacher Chapter14.Section03.FaithfulSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- In the two-core-kernel case, an active original residual actor selects one factor. -/
theorem centralizer_thompson_single_factor_of_twoCore_kernel
    (h₀ : Hypothesis1331 T L) {z : G}
    (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (R : Subgroup G) (hRT : R ≤ T)
    (hnR : (T : Subgroup G) ≤ normalizer (R : Set G))
    (hQR : (centralizer ({z} : Set G)).pCoreIn 2 ≤ R)
    (hJ : ¬ elementaryAbelianMaxJ R ≤ centralizer (centralizerOmegaOrbit T z : Set G))
    (hsolv : Group.IsSolvable (centralizer ({z} : Set G)))
    (hkernel : centralizer ((centralizerOmegaOrbit T z).subgroupOf
      (centralizer ({z} : Set G)) : Set (centralizer ({z} : Set G))) =
      pCore 2 (centralizer ({z} : Set G)))
    (A : Subgroup G) (hAH : A ≤ centralizer ({z} : Set G))
    (hA : IsPPerfect 2 A)
    (horder : ∃ m n : ℕ, Nat.card A ∣ 2 ^ m * 3 ^ n)
    (hAN : A ≤ normalizer (R : Set G))
    (hAmove : ¬ A ≤ centralizer (centralizerOmegaOrbit T z : Set G)) :
    let H := centralizer ({z} : Set G)
    let U := (centralizerOmegaOrbit T z).subgroupOf H
    letI := (centralizerOmegaOrbit_reduced h₀ hz hz1).normal
    let q := QuotientGroup.mk' (centralizer (U : Set H))
    Nonempty ((((conjugateSpanBy (elementaryAbelianMaxJ R) H).subgroupOf H).map q) ≃*
      Equiv.Perm (Fin 3)) := by
  let H := centralizer ({z} : Set G)
  let U := (centralizerOmegaOrbit T z).subgroupOf H
  let := (centralizerOmegaOrbit_reduced h₀ hz hz1).normal
  let q := QuotientGroup.mk' (centralizer (U : Set H))
  let N := conjugateSpanBy (elementaryAbelianMaxJ R) H
  let I := (N.subgroupOf H).map q
  let J := ((elementaryAbelianMaxJ R).subgroupOf H).map q
  let B := (A.subgroupOf H).map q
  have hJH : elementaryAbelianMaxJ R ≤ H :=
    (sSup_le fun _ hB => hB.1).trans (hRT.trans (original_sylow_le_centralizer hz))
  have hNH : N ≤ H := conjugateSpanBy_le_self hJH
  let : (N.subgroupOf H).Normal :=
    (normal_subgroupOf_iff_le_normalizer hNH).mpr (le_normalizer_conjugateSpanBy _ _)
  let : I.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hm := centralizer_thompson_span_models h₀ hz hz1 R hRT hQR hJ hsolv
  obtain ⟨P,hP⟩ := centralizer_thompson_span_sylow h₀ hz hz1 R hRT hnR hQR hJ hsolv
  have hBi : IsPPerfect 2 (A.subgroupOf H) :=
    hA.of_surjective (subgroupOfEquivOfLe hAH).symm.toMonoidHom
      (subgroupOfEquivOfLe hAH).symm.surjective
  have hB : IsPPerfect 2 B := hBi.of_surjective (q.subgroupMap (A.subgroupOf H))
    (q.subgroupMap_surjective _)
  have hB1 : B ≠ ⊥ := by
    intro hb
    have ha : A.subgroupOf H ≤ q.ker := (Subgroup.map_eq_bot_iff _).mp hb
    apply hAmove
    intro a haA v hv
    have hk : (⟨a,hAH haA⟩ : H) ∈ centralizer (U : Set H) := by
      have hh := ha (show (⟨a,hAH haA⟩ : H) ∈ A.subgroupOf H from haA)
      rwa [QuotientGroup.ker_mk'] at hh
    exact congrArg Subtype.val (hk ⟨v,centralizerOmegaOrbit_le hz hv⟩ hv)
  have ho : ∃ m n : ℕ, Nat.card B ∣ 2 ^ m * 3 ^ n := by
    obtain ⟨m,n,hh⟩ := horder
    refine ⟨m,n,(card_map_dvd (A.subgroupOf H) q).trans ?_⟩
    rwa [Nat.card_congr (subgroupOfEquivOfLe hAH).toEquiv]
  have hrank : primeRank 3 H ≤ 2 :=
    (isQuasithin_iff_twoLocal.mp h₀.qtke.quasithin) H
      (isTwoLocal_involution_centralizer
        (orderOf_eq_prime ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.1 hz1))
      3 (by decide) (by decide)
  have hqrank : primeRank 3 (H ⧸ centralizer (U : Set H)) ≤ 2 := by
    rw [primeRank_congr 3 (QuotientGroup.quotientMulEquivOfEq hkernel)]
    exact (primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup).trans hrank
  have hn : B ≤ normalizer (J : Set _) := by
    have hAi : A.subgroupOf H ≤ normalizer ((elementaryAbelianMaxJ R).subgroupOf H : Set H) := by
      rw [← subgroupOf_normalizer_eq hJH]
      exact subgroupOf_mono H (hAN.trans (normalizer_le_normalizer_elementaryAbelianMaxJ R))
    exact (map_mono hAi).trans (((elementaryAbelianMaxJ R).subgroupOf H).le_normalizer_map q)
  exact SymmetricThreeFactorSelection.single_of_twoPerfect_actor I J B hm P hP hB hB1 ho hqrank hn


/-- The actual action kernel is the two-core of the original ambient Thompson span. -/
theorem centralizer_thompson_core_quotient_of_twoCore_kernel
    (h₀ : Hypothesis1331 T L) {z : G}
    (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (R : Subgroup G) (hRT : R ≤ T)
    (hnR : (T : Subgroup G) ≤ normalizer (R : Set G))
    (hQR : (centralizer ({z} : Set G)).pCoreIn 2 ≤ R)
    (hJ : ¬ elementaryAbelianMaxJ R ≤ centralizer (centralizerOmegaOrbit T z : Set G))
    (hsolv : Group.IsSolvable (centralizer ({z} : Set G)))
    (hkernel : centralizer ((centralizerOmegaOrbit T z).subgroupOf
      (centralizer ({z} : Set G)) : Set (centralizer ({z} : Set G))) =
      pCore 2 (centralizer ({z} : Set G)))
    (A : Subgroup G) (hAH : A ≤ centralizer ({z} : Set G))
    (hA : IsPPerfect 2 A)
    (horder : ∃ m n : ℕ, Nat.card A ∣ 2 ^ m * 3 ^ n)
    (hAN : A ≤ normalizer (R : Set G))
    (hAmove : ¬ A ≤ centralizer (centralizerOmegaOrbit T z : Set G)) :
    let I := conjugateSpanBy (elementaryAbelianMaxJ R) (centralizer ({z} : Set G))
    Nonempty ((I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 3)) := by
  let H := centralizer ({z} : Set G)
  let U := (centralizerOmegaOrbit T z).subgroupOf H
  let := (centralizerOmegaOrbit_reduced h₀ hz hz1).normal
  let q := QuotientGroup.mk' (centralizer (U : Set H))
  let I := conjugateSpanBy (elementaryAbelianMaxJ R) H
  let N := I.subgroupOf H
  obtain ⟨e⟩ := centralizer_thompson_single_factor_of_twoCore_kernel
    h₀ hz hz1 R hRT hnR hQR hJ hsolv hkernel A hAH hA horder hAN hAmove
  let f : N →* Equiv.Perm (Fin 3) := e.toMonoidHom.comp (q.subgroupMap N)
  have hf : Function.Surjective f := e.surjective.comp (q.subgroupMap_surjective N)
  have hk : f.ker = (pCore 2 H).subgroupOf N := by
    ext x
    change e (q.subgroupMap N x) = 1 ↔ x.val ∈ pCore 2 H
    rw [← e.map_one, e.injective.eq_iff]
    rw [Subtype.ext_iff]
    change q x.val = 1 ↔ x.val ∈ pCore 2 H
    change x.val ∈ q.ker ↔ x.val ∈ pCore 2 H
    rw [QuotientGroup.ker_mk', hkernel]
  have hkp : IsPGroup 2 f.ker := by
    rw [hk]
    exact pCore_isPGroup.comap_subtype
  have hc := ker_eq_twoCore_of_surjective_perm_three f hf hkp
  let eN : (N ⧸ pCore 2 N) ≃* Equiv.Perm (Fin 3) :=
    (QuotientGroup.quotientMulEquivOfEq hc.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have hIH : I ≤ H := conjugateSpanBy_le_self
    ((sSup_le fun _ hB => hB.1).trans (hRT.trans (original_sylow_le_centralizer hz)))
  let eI : N ≃* I := subgroupOfEquivOfLe hIH
  exact ⟨(QuotientGroup.congr _ _ eI (pCore_map_iso 2 eI)).symm.trans eN⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable

namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Stellmacher Chapter14.Section03.FaithfulSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The literal O^{3′}(C_L(z)), embedded in the original ambient group. -/
def firstCentralizerResidual (L : Subgroup G) (z : G) : Subgroup G :=
  (primeToResidual 3 (L ⊓ centralizer ({z} : Set G) : Subgroup G)).map
    (L ⊓ centralizer ({z} : Set G)).subtype

omit [Finite G] in
/-- The literal residual equation, retaining the original inclusion into G. -/
theorem firstCentralizerResidual_eq (L : Subgroup G) (z : G) :
    firstCentralizerResidual L z =
      (primeToResidual 3 (L ⊓ centralizer ({z} : Set G) : Subgroup G)).map
        (L ⊓ centralizer ({z} : Set G)).subtype := by rfl

omit [Finite G] in
/-- The source residual stays in its original component centralizer. -/
theorem firstCentralizerResidual_le (L : Subgroup G) (z : G) :
    firstCentralizerResidual L z ≤ L ⊓ centralizer ({z} : Set G) :=
  map_subtype_le _

/-- The literal prime-to-three residual has no nontrivial two-group quotient. -/
theorem firstCentralizerResidual_twoPerfect (L : Subgroup G) (z : G) :
    IsPPerfect 2 (firstCentralizerResidual L z) := by
  let C := L ⊓ centralizer ({z} : Set G)
  exact (isPPerfect_primeToResidual (G := C) 3 2 (by decide)).of_surjective
    (C.subtype.subgroupMap (primeToResidual 3 C)) (C.subtype.subgroupMap_surjective _)

/-- A cubic divisor prevents the original residual from lying in the two-group action kernel. -/
theorem firstCentralizerResidual_noncentral_of_twoCore_kernel {z : G}
    (hkernel : centralizer ((centralizerOmegaOrbit T z).subgroupOf
      (centralizer ({z} : Set G)) : Set (centralizer ({z} : Set G))) =
      pCore 2 (centralizer ({z} : Set G)))
    (hthree : 3 ∣ Nat.card (firstCentralizerResidual L z)) :
    ¬ firstCentralizerResidual L z ≤ centralizer (centralizerOmegaOrbit T z : Set G) := by
  let H := centralizer ({z} : Set G)
  let A := firstCentralizerResidual L z
  have hAH : A ≤ H := (map_subtype_le _).trans inf_le_right
  intro hcent
  have hAcore : A ≤ H.pCoreIn 2 := by
    intro a ha
    have hc : (⟨a,hAH ha⟩ : H) ∈ centralizer
        ((centralizerOmegaOrbit T z).subgroupOf H : Set H) := by
      intro v hv
      exact Subtype.ext (hcent ha v.val hv)
    exact mem_map_of_mem H.subtype (hkernel ▸ hc)
  have hp : IsPGroup 2 A := (isPGroup_pCoreIn 2 H).to_le hAcore
  obtain ⟨n,hn⟩ := hp.exists_card_eq
  have hd : 3 ∣ 2 ^ n := hn ▸ hthree
  exact (by decide : ¬ (3 : ℕ) ∣ 2) (Nat.Prime.dvd_of_dvd_pow (by decide) hd)

/-- Apply single-factor selection to the literal source L₁=O^{3′}(C_L(z)). -/
theorem centralizer_thompson_core_quotient_of_firstResidual
    (h₀ : Hypothesis1331 T L) {z : G}
    (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (R : Subgroup G) (hRT : R ≤ T)
    (hnR : (T : Subgroup G) ≤ normalizer (R : Set G))
    (hQR : (centralizer ({z} : Set G)).pCoreIn 2 ≤ R)
    (hJ : ¬ elementaryAbelianMaxJ R ≤ centralizer (centralizerOmegaOrbit T z : Set G))
    (hsolv : Group.IsSolvable (centralizer ({z} : Set G)))
    (hkernel : centralizer ((centralizerOmegaOrbit T z).subgroupOf
      (centralizer ({z} : Set G)) : Set (centralizer ({z} : Set G))) =
      pCore 2 (centralizer ({z} : Set G)))
    (horder : ∃ m n : ℕ, Nat.card (firstCentralizerResidual L z) ∣ 2 ^ m * 3 ^ n)
    (hthree : 3 ∣ Nat.card (firstCentralizerResidual L z))
    (hAN : firstCentralizerResidual L z ≤ normalizer (R : Set G)) :
    let I := conjugateSpanBy (elementaryAbelianMaxJ R) (centralizer ({z} : Set G))
    Nonempty ((I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 3)) := by
  exact centralizer_thompson_core_quotient_of_twoCore_kernel h₀ hz hz1 R hRT hnR hQR hJ hsolv
    hkernel (firstCentralizerResidual L z) ((map_subtype_le _).trans inf_le_right)
    (firstCentralizerResidual_twoPerfect L z) horder hAN
    (firstCentralizerResidual_noncentral_of_twoCore_kernel hkernel hthree)

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
