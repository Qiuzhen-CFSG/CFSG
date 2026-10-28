module

public import Theory.GroupTheory.SymmetricThreeResidualRank
public import Theory.GroupTheory.SymmetricThreeResidualNormality
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.CoveredIntersection
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.OrdinaryRow

/-!
# Covered-row residual disjointness and ordinary-row selection

For H = C_G(z), suppose the kernel of its action on V_H is O₂(H).
The intersection of the odd Thompson residual with the actual L₁ image
has a normal two-perfect lift inside L₁. The earlier 13.3.9 conclusion
identifies a nontrivial lift with the selected residual actor, which
normalizes R₁. The marked Thompson Sylow then excludes that lift.

Residual disjointness selects a single Thompson factor and forces
m₃(L₁) = 1. The five-dimensional core marking excludes the triple cover,
so L/O₂(L) is A₆. The final theorem applies this row selection to the
literal H/O₂(H) ≅ S₃ × S₃ quotient and H = L₁IT product. It uses only
L₁,+ normalization before selecting the ordinary row; full L₁
normalization is required only after that selection.

The earlier 13.3.9 and 13.4.2 inputs remain explicit, as do the
Baumann-normalizer bound and the two-core action-kernel alternative.
Their final source discharge belongs to the fixed-core assembly.
Source: Aschbacher–Smith, 13.3.9 and 13.4.8, printed pp.887 and 904–905.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02 Stellmacher Chapter14.Section03.FaithfulSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
/-- The original Sylow subgroup normalizes the literal centralizer residual L₁. -/
theorem firstCentralizerResidual_sylow_normalizes
    (D : ChosenModule T L V) {z : G}
    (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G)) :
    (T : Subgroup G) ≤ normalizer (firstCentralizerResidual L z : Set G) := by
  let H := centralizer ({z} : Set G)
  let C := L ⊓ H
  have hn : (T : Subgroup G) ≤ normalizer (C : Set G) :=
    (le_inf D.sylow_normalizes_component
      ((original_sylow_le_centralizer hz).trans H.le_normalizer)).trans inf_normalizer_le_normalizer_inf
  rw [firstCentralizerResidual_eq]
  exact hn.trans (normalizer_le_normalizer_characteristic_image C (primeToResidual 3 C))

/-- The earlier normal-subgroup classification excludes the full L₁ residual intersection. -/
theorem centralizer_thompson_residual_disjoint_of_source1339
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) {z : G}
    (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (R : Subgroup G) (hRT : R ≤ T)
    (hnR : (T : Subgroup G) ≤ normalizer (R : Set G))
    (hQR : (centralizer ({z} : Set G)).pCoreIn 2 ≤ R)
    (hJ : ¬ elementaryAbelianMaxJ R ≤ centralizer (centralizerOmegaOrbit T z : Set G))
    (hsolv : Group.IsSolvable (centralizer ({z} : Set G)))
    (hkernel : centralizer ((centralizerOmegaOrbit T z).subgroupOf
      (centralizer ({z} : Set G)) : Set (centralizer ({z} : Set G))) =
      pCore 2 (centralizer ({z} : Set G)))
    (Aplus : Subgroup G) (hAN : Aplus ≤ normalizer (R : Set G))
    (h1339 : ∀ Y : Subgroup G, Y ≤ centralizer ({z} : Set G) →
      centralizer ({z} : Set G) ≤ normalizer (Y : Set G) →
      Y ≤ normalizer (L : Set G) → IsPPerfect 2 Y → Y = ⊥ ∨ Y = Aplus) :
    let H := centralizer ({z} : Set G)
    let U := (centralizerOmegaOrbit T z).subgroupOf H
    letI := (centralizerOmegaOrbit_reduced h₀ hz hz1).normal
    let q := QuotientGroup.mk' (centralizer (U : Set H))
    let I := ((conjugateSpanBy (elementaryAbelianMaxJ R) H).subgroupOf H).map q
    Disjoint ((pResidual 2 I).map I.subtype) ((firstCentralizerResidual L z).subgroupOf H |>.map q) := by
  let H := centralizer ({z} : Set G)
  let U := (centralizerOmegaOrbit T z).subgroupOf H
  let := (centralizerOmegaOrbit_reduced h₀ hz hz1).normal
  let q := QuotientGroup.mk' (centralizer (U : Set H))
  let N := conjugateSpanBy (elementaryAbelianMaxJ R) H
  let I := (N.subgroupOf H).map q
  let A := (firstCentralizerResidual L z).subgroupOf H
  have hTH : (T : Subgroup G) ≤ H := original_sylow_le_centralizer hz
  have hNH : N ≤ H := conjugateSpanBy_le_self
    ((sSup_le fun _ hA => hA.1).trans (hRT.trans hTH))
  let : (N.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hNH).mpr
    (le_normalizer_conjugateSpanBy _ _)
  let : I.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hAH : firstCentralizerResidual L z ≤ H := (firstCentralizerResidual_le L z).trans inf_le_right
  have hSA : (T.subtype hTH : Subgroup H) ≤ normalizer (A : Set H) := by
    rw [← subgroupOf_normalizer_eq hAH]
    exact subgroupOf_mono H (firstCentralizerResidual_sylow_normalizes D hz)
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk',hkernel]
    exact pCore_isPGroup
  obtain ⟨Y,hYn,hYp,hYA,hYm⟩ := SymmetricThreeCubicNormality.residual_intersection_lift
    q (QuotientGroup.mk'_surjective _) hk I
    (centralizer_thompson_span_models h₀ hz hz1 R hRT hQR hJ hsolv)
    (T.subtype hTH) A hSA
  let Z := Y.map H.subtype
  have hZH : Z ≤ H := map_subtype_le _
  have hZA : Z ≤ firstCentralizerResidual L z := by
    have hh := map_mono (f := H.subtype) hYA
    rwa [map_subgroupOf_eq_of_le hAH] at hh
  have hZN : H ≤ normalizer (Z : Set G) := by
    let := hYn
    have hh := (map_mono (show (⊤ : Subgroup H) ≤ normalizer (Y : Set H)
      from le_normalizer_of_normal)).trans (Y.le_normalizer_map H.subtype)
    simpa only [← MonoidHom.range_eq_map,range_subtype] using hh
  have hZp : IsPPerfect 2 Z := hYp.of_surjective (H.subtype.subgroupMap Y)
    (H.subtype.subgroupMap_surjective Y)
  have hs : Z.subgroupOf H = Y := comap_map_eq_self_of_injective H.subtype_injective Y
  apply disjoint_iff.mpr
  change ((pResidual 2 I).map I.subtype) ⊓ A.map q = ⊥
  rw [← hYm]
  rcases h1339 Z hZH hZN (hZA.trans ((firstCentralizerResidual_le L z).trans
      (inf_le_left.trans L.le_normalizer))) hZp with he | he
  · have hy : Y = ⊥ := by
      apply map_injective H.subtype_injective
      simpa only [Subgroup.map_bot] using he
    rw [hy,Subgroup.map_bot]
  · have hd := centralizer_thompson_residual_disjoint_normalizing_actor h₀ hz hz1 R
      hRT hnR hQR hJ hsolv Z (he ▸ hAN)
    change Disjoint ((pResidual 2 I).map I.subtype) ((Z.subgroupOf H).map q) at hd
    rw [hs] at hd
    exact disjoint_self.mp (hd.mono_left (hYm ▸ inf_le_left))
/-- The two-core action kernel and the earlier classification force m₃(L₁) = 1. -/
theorem centralizer_firstResidual_threeRank_of_source1339
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) {z : G}
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
    (Aplus : Subgroup G) (hAN : Aplus ≤ normalizer (R : Set G))
    (h1339 : ∀ Y : Subgroup G, Y ≤ centralizer ({z} : Set G) →
      centralizer ({z} : Set G) ≤ normalizer (Y : Set G) →
      Y ≤ normalizer (L : Set G) → IsPPerfect 2 Y → Y = ⊥ ∨ Y = Aplus) :
    primeRank 3 (firstCentralizerResidual L z) = 1 := by
  let H := centralizer ({z} : Set G)
  let U := (centralizerOmegaOrbit T z).subgroupOf H
  let := (centralizerOmegaOrbit_reduced h₀ hz hz1).normal
  let q := QuotientGroup.mk' (centralizer (U : Set H))
  let N := conjugateSpanBy (elementaryAbelianMaxJ R) H
  let I := (N.subgroupOf H).map q
  let A := firstCentralizerResidual L z
  let B := (A.subgroupOf H).map q
  have hAH : A ≤ H := (firstCentralizerResidual_le L z).trans inf_le_right
  have hpA := firstCentralizerResidual_twoPerfect L z
  have hpAi : IsPPerfect 2 (A.subgroupOf H) := hpA.of_surjective
    (subgroupOfEquivOfLe hAH).symm.toMonoidHom (subgroupOfEquivOfLe hAH).symm.surjective
  have hpB : IsPPerfect 2 B := hpAi.of_surjective (q.subgroupMap (A.subgroupOf H))
    (q.subgroupMap_surjective _)
  have hJH : elementaryAbelianMaxJ R ≤ H :=
    (sSup_le fun _ hB => hB.1).trans (hRT.trans (original_sylow_le_centralizer hz))
  have hNH : N ≤ H := conjugateSpanBy_le_self hJH
  let : (N.subgroupOf H).Normal :=
    (normal_subgroupOf_iff_le_normalizer hNH).mpr (le_normalizer_conjugateSpanBy _ _)
  let : I.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hB1 : B ≠ ⊥ := by
    intro hb
    have ha : A.subgroupOf H ≤ q.ker := (Subgroup.map_eq_bot_iff _).mp hb
    apply firstCentralizerResidual_noncentral_of_twoCore_kernel hkernel hthree
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
  have hd := centralizer_thompson_residual_disjoint_of_source1339 h₀ D hz hz1 R hRT hnR hQR
    hJ hsolv hkernel Aplus hAN h1339
  have hBrank : primeRank 3 B ≤ 1 := (SymmetricThreeCubicNormality.single_and_rank_of_residual_disjoint
    I B (centralizer_thompson_span_models h₀ hz hz1 R hRT hQR hJ hsolv) hpB hB1 ho hqrank hd).2
  let f := q.subgroupMap (A.subgroupOf H)
  have hk : IsPGroup 2 f.ker := by
    rw [ker_subgroupMap, QuotientGroup.ker_mk', hkernel]
    exact pCore_isPGroup.comap_subtype
  have hAiRank : primeRank 3 (A.subgroupOf H) ≤ 1 := by
    apply (primeRank_le_of_coprime_ker 3 f ?_).trans hBrank
    obtain ⟨n,hn⟩ := hk.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hArank : primeRank 3 A ≤ 1 := by
    rwa [primeRank_congr 3 (subgroupOfEquivOfLe hAH)] at hAiRank
  have hne : primeRank 3 A ≠ 0 := fun he => PrimeRank.eq_zero_iff_not_dvd_card.mp he hthree
  change primeRank 3 A = 1
  omega

open Section08.TransvectionRecognition.Component.ModelExtension in
/-- The five-dimensional marking and residual rank exclude the covered A₆ row. -/
theorem ordinary_of_centralizer_source1339
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    [IsQuasisimple (L ⧸ pCore 2 L)]
    (v : V) (hz : v.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : v.val ∉ centralizer (L : Set G))
    (R : Subgroup G) (hRT : R ≤ T)
    (hnR : (T : Subgroup G) ≤ normalizer (R : Set G))
    (hQR : (centralizer ({v.val} : Set G)).pCoreIn 2 ≤ R)
    (hJ : ¬ elementaryAbelianMaxJ R ≤ centralizer (centralizerOmegaOrbit T v.val : Set G))
    (hsolv : Group.IsSolvable (centralizer ({v.val} : Set G)))
    (hkernel : centralizer ((centralizerOmegaOrbit T v.val).subgroupOf
      (centralizer ({v.val} : Set G)) : Set (centralizer ({v.val} : Set G))) =
      pCore 2 (centralizer ({v.val} : Set G)))
    (Aplus : Subgroup G) (hAN : Aplus ≤ normalizer (R : Set G))
    (h1339 : ∀ Y : Subgroup G, Y ≤ centralizer ({v.val} : Set G) →
      centralizer ({v.val} : Set G) ≤ normalizer (Y : Set G) →
      Y ≤ normalizer (L : Set G) → IsPPerfect 2 Y → Y = ⊥ ∨ Y = Aplus) :
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨horder,hthree⟩ := firstCentralizerResidual_order_of_marking D m v hzL
  have hr := centralizer_firstResidual_threeRank_of_source1339 h₀ D hz
    (fun he => hzL (he ▸ one_mem _)) R hRT hnR hQR hJ hsolv hkernel
    horder hthree Aplus hAN h1339
  exact ordinary_of_firstCentralizerResidual_threeRank D m v hzL hr.le

open Chapter12.Section02
open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement

universe u
/-- The source row selection supplies the literal pair quotient and local product. -/
theorem centralizer_pair_quotient_of_source_row_selection
    {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (v : V) (hz : v.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : v.val ∉ centralizer (L : Set G))
    {K : Type*} [Group K] (f : T →* K) (R : Subgroup G)
    (hR : R = ((pCore 2 K).comap f).map (T : Subgroup G).subtype)
    (hQR : (centralizer ({v.val} : Set G)).pCoreIn 2 ≤ R)
    (hsolv : Group.IsSolvable (centralizer ({v.val} : Set G)))
    (hkernel : centralizer ((centralizerOmegaOrbit T v.val).subgroupOf
      (centralizer ({v.val} : Set G)) : Set (centralizer ({v.val} : Set G))) =
      pCore 2 (centralizer ({v.val} : Set G)))
    (hB : normalizer (ChapterB.baumann R : Set G) ≤ normalizer (L : Set G))
    (hout : ¬ centralizer ({v.val} : Set G) ≤ normalizer (L : Set G))
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hordinaryN : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) →
      firstCentralizerResidual L v.val ≤ normalizer (R : Set G))
    (hcoveredN : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) →
      plus L (T : Subgroup G) (V ⊓ omegaOneCenterAmbient (T : Subgroup G)) ≤ normalizer (R : Set G))
    (hcovered1339 : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) →
      ∀ Y : Subgroup G, Y ≤ centralizer ({v.val} : Set G) →
      centralizer ({v.val} : Set G) ≤ normalizer (Y : Set G) →
      Y ≤ normalizer (L : Set G) → IsPPerfect 2 Y →
      Y = ⊥ ∨ Y = plus L (T : Subgroup G) (V ⊓ omegaOneCenterAmbient (T : Subgroup G)))
    (h1339 : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) →
      ∀ Y : Subgroup G, Y ≤ centralizer ({v.val} : Set G) →
      centralizer ({v.val} : Set G) ≤ normalizer (Y : Set G) →
      Y ≤ normalizer (L : Set G) → IsPPerfect 2 Y →
      Y = ⊥ ∨ Nat.card (Y ⧸ pCore 2 Y) = 3)
    (h1342 : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) →
      (primeToResidual 3 (normalizer (L : Set G))).map
        (normalizer (L : Set G)).subtype = L) :
    let H := centralizer ({v.val} : Set G)
    let I := conjugateSpanBy (elementaryAbelianMaxJ R) H
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
      Nonempty ((H ⧸ pCore 2 H) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∧
      Nonempty ((I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 3)) ∧
      Representation.BinaryOffender.rank (⁅centralizerOmegaOrbit T v.val,I⁆ : Subgroup G) = 2 ∧
      H = firstCentralizerResidual L v.val ⊔ I ⊔ (T : Subgroup G) := by
  classical
  let := h.quasisimple
  have ordinary : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) := by
    by_contra hn
    have hz1 : v.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
    have hRT : R ≤ T := by rw [hR]; exact map_subtype_le _
    have hnR : (T : Subgroup G) ≤ normalizer (R : Set G) := by
      rw [hR]
      have hh := (map_mono (show (⊤ : Subgroup T) ≤ normalizer ((pCore 2 K).comap f : Set T)
        from le_normalizer_of_normal)).trans
          (((pCore 2 K).comap f).le_normalizer_map (T : Subgroup G).subtype)
      simpa only [← MonoidHom.range_eq_map,range_subtype] using hh
    let H := centralizer ({v.val} : Set G)
    let U := (centralizerOmegaOrbit T v.val).subgroupOf H
    have hRH : R ≤ H := hRT.trans (original_sylow_le_centralizer hz)
    have hcore : R ⊓ centralizer (centralizerOmegaOrbit T v.val : Set G) = H.pCoreIn 2 := by
      apply le_antisymm
      · intro a ha
        have hc : (⟨a,hRH ha.1⟩ : H) ∈ centralizer (U : Set H) := by
          intro v hv
          exact Subtype.ext (ha.2 v.val hv)
        exact mem_map_of_mem H.subtype (hkernel ▸ hc)
      · intro a ha
        refine ⟨hQR ha, ?_⟩
        obtain ⟨b,hb,rfl⟩ := ha
        have hc : b ∈ centralizer (U : Set H) := hkernel.symm ▸ hb
        intro v hv
        exact congrArg Subtype.val (hc ⟨v,centralizerOmegaOrbit_le hz hv⟩ hv)
    have hJ := centralizer_thompson_noncentral_of_baumann_bound h₀ hz hz1 R hRT hcore hB hout
    exact hn (ordinary_of_centralizer_source1339 h₀ D m v hz hzL R hRT hnR hQR hJ hsolv
      hkernel _ (hcoveredN hn) (hcovered1339 hn))
  exact ⟨ordinary,centralizer_pair_quotient_of_baumann_bound h₀ h structural D m ordinary v hz hzL
    f R hR hQR hsolv hkernel hB hout hindex (hordinaryN ordinary) (h1339 ordinary) (h1342 ordinary)⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
