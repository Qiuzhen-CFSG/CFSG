module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootFF.Classification
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The cubic Cartan prime and the actual secondary quotient

When three divides the Cartan order, the secondary two-core quotient has
trivial center. The A.3.6 alternative with center of order three is impossible:
in the same ambient two-core quotient, this center and the outside Cartan
cubic form an elementary nine centralizing the embedded centerless SL₂ Levi.
The Levi contributes another cubic rank, contradicting the SQTK bound.

Consequently both the faithful module-action projection and the A.3.18 star
projection have precisely the intrinsic two-core as kernel. Their induced
isomorphism agrees on original elements and preserves odd-prime ranks. The
literal high-rank source alternative therefore transfers to the actual FF
actor. Its center and three-rank also exclude every binary SL₃ marking.
The remaining projective-family exclusion and full action-table comparison
belong to the subsequent ordinary-root assembly.

Source: Aschbacher–Smith 4.3.6, printed p.615; A.3.6 and A.3.18,
printed pp.43–45 and 51–53; the quotient comparison preceding B.5.6(1).
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootFF

private theorem no_cubic_center_with_fixed_levi
    {H : Type*} [Group H] [Finite H]
    (K P : Subgroup H) [K.Normal] (hPK : P ≤ K)
    (hzP : center P = ⊥) (hd : 3 ∣ Nat.card P)
    (a : H) (ha : orderOf a = 3) (haK : a ∉ K)
    (hc : a ∈ centralizer (P : Set H)) (hr : primeRank 3 H ≤ 2)
    (hz : Nat.card (center K) = 3) : False := by
  let Z := (center K).map K.subtype
  let : Z.Normal := inferInstanceAs (((center K).map K.subtype).Normal)
  have hZ : Nat.card Z = 3 := by rw [card_map_of_injective K.subtype_injective, hz]
  let : IsCyclic Z := isCyclic_of_prime_card hZ
  let : IsElementaryAbelian 3 Z :=
    ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun z => hZ ▸ pow_card_eq_one' (x := z))⟩
  have hzfix : Z ≤ centralizer ({a} : Set H) := by
    let f : H →* MulAut Z := MulAut.conjNormal
    have hthree : orderOf (f a) ∣ 3 := ha ▸ orderOf_map_dvd f a
    have htwo : orderOf (f a) ∣ 2 := by
      have hh := orderOf_dvd_natCard (f a)
      rwa [IsCyclic.card_mulAut, hZ, Nat.totient_prime Nat.prime_three] at hh
    have he : f a = 1 := orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 3 2) hthree htwo)
    intro z hz
    have hh := congrArg (fun t : MulAut Z => (t (⟨z,hz⟩ : Z) : H)) he
    change a * z * a⁻¹ = z at hh
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hh).symm
  obtain ⟨hE,hcard⟩ := IsElementaryAbelian.fixed_join_card Z a ha
    (Z.disjoint_zpowers_of_prime_order_not_mem a ha
      (fun h => haK (map_subtype_le _ h))) hzfix
    (by simpa only [pow_one] using hZ : Nat.card Z = 3 ^ 1)
  let := hE
  have hE2 : 2 ≤ primeRank 3 (Z ⊔ zpowers a : Subgroup H) := by
    let E := Z ⊔ zpowers a
    let : IsElementaryAbelian 3 (⊤ : Subgroup E) :=
      ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x =>
        Subtype.ext (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 3 E) x.val))⟩
    have ht : Nat.card (⊤ : Subgroup E) = 3 ^ 2 := by
      rw [Nat.card_congr topEquiv.toEquiv]
      exact hcard
    exact IsElementaryAbelian.primeRank_ge_of_card (⊤ : Subgroup E) ht
  have hZP : Z ≤ centralizer (P : Set H) := by
    rintro z ⟨x,hx,rfl⟩ y hy
    exact congrArg Subtype.val (mem_center_iff.mp hx (⟨y,hPK hy⟩ : K))
  have hcop : Nat.Coprime 3 (Nat.card (center P)) := by rw [hzP]; simp
  have hsum := ResidualCentralizerRank.primeRank_add_le_of_center_coprime
    (Z ⊔ zpowers a) P (sup_le hZP (zpowers_le.mpr hc)) hcop
  have hP : 1 ≤ primeRank 3 P := by
    by_contra! he
    exact (PrimeRank.eq_zero_iff_not_dvd_card.mp (by omega : primeRank 3 P = 0)) hd
  omega

open ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ} (m : OrdinarySymplecticMarking c n)

/-- The cubic Cartan actor excludes the central three-cover alternative. -/
theorem secondary_twoCore_center_eq_bot_of_three_dvd
    (hn : 1 < n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G))
    (hJK : m.second ≤ KZ)
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (hd : 3 ∣ 2 ^ n - 1) : center (KZ ⧸ pCore 2 KZ) = ⊥ := by
  obtain ⟨a, haY, ha, haK⟩ := exists_cartan_prime_actor m KZ hK Nat.prime_three hd
  let E := KZ ⊔ zpowers a
  let K := KZ.subgroupOf E
  have hKN := hK.trans (Subgroup.centralizer_le_normalizer _)
  have hEN : E ≤ m.rootNormalizer := sup_le hKN
    (zpowers_le.mpr (rootTorus_le_normalizer m haY))
  let : K.Normal := normal_subgroupOf_of_le_normalizer (hEN.trans hnormal)
  let e : K ≃* KZ := subgroupOfEquivOfLe (show KZ ≤ E from le_sup_left)
  let eq : (K ⧸ pCore 2 K) ≃* KZ ⧸ pCore 2 KZ :=
    QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  let := hquasi
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv eq.symm
  have hkc : K.IsCComponent := secondary_cComponent_in_extension m KZ E hK hcomp le_sup_left hEN
  have hsq : IsSQTK KnownSimple.IsKnownSimple E :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hEN)).mp
      ((h.simpleQTKE.twoLocal_sqtk (m.rootNormalizer_twoLocal hn)).subgroup
        (E.subgroupOf m.rootNormalizer))
  have hz : center (twoCoreComponent K) = ⊥ := by
    rcases twoCore_center_cases hsq hkc with hz | ⟨⟨ez⟩,_⟩
    · exact hz
    exfalso
    let q := QuotientGroup.mk' (pCore 2 E)
    let j : Matrix.SpecialLinearGroup (Fin 2) m.Field →* E :=
      m.leviEmbedding.codRestrict E (fun b =>
        (le_sup_left : KZ ≤ E) (hJK (m.leviEmbedding_range_le_second hn ⟨b,rfl⟩)))
    let f := q.comp j
    have hf : Function.Injective f :=
      m.levi_injective_mod_twoCore hn E (hJK.trans le_sup_left)
    let P := f.range
    let ep : Matrix.SpecialLinearGroup (Fin 2) m.Field ≃* P := MonoidHom.ofInjective hf
    let := m.levi_simple hn
    let := m.levi_perfect hn
    let : IsSimpleGroup P := ep.symm.isSimpleGroup
    let : Group.IsPerfect P := Group.IsPerfect.ofSurjective (f := f.rangeRestrict)
      f.rangeRestrict_surjective
    have hzP : center P = ⊥ := by
      rcases (inferInstance : (center P).Normal).eq_bot_or_eq_top with hb | ht
      · exact hb
      · exact (Group.IsPerfect.not_isMulCommutative P (center_eq_top_iff.mp ht)).elim
    have hPK : P ≤ twoCoreComponent K := by
      rintro _ ⟨b,rfl⟩
      exact mem_map_of_mem q (hJK (m.leviEmbedding_range_le_second hn ⟨b,rfl⟩))
    have hdP : 3 ∣ Nat.card P := by
      rw [← Nat.card_congr ep.toEquiv,
        Nat.card_congr (MonoidHom.ofInjective m.leviEmbedding_injective).toEquiv]
      exact m.scalar_prime_dvd_levi hd
    let a' : E := ⟨a,(le_sup_right : zpowers a ≤ E) (mem_zpowers a)⟩
    have ha' : orderOf a' = 3 := (orderOf_injective E.subtype E.subtype_injective a').symm.trans ha
    have hqa := twoCore_actor (K := K) Nat.prime_three (by decide : Odd 3) a' ha' haK
    have hfix : q a' ∈ centralizer (P : Set (TwoCoreQuotient E)) := by
      rintro _ ⟨b,rfl⟩
      apply congrArg q
      apply Subtype.ext
      exact m.cartan_centralizes_levi haY (m.leviEmbedding b) ⟨b,rfl⟩
    have hzc : Nat.card (center (twoCoreComponent K)) = 3 := by
      rw [Nat.card_congr ez.toEquiv]
      exact Nat.card_zmod 3
    let : (twoCoreComponent K).Normal := twoCore_normal K
    exact no_cubic_center_with_fixed_levi (twoCoreComponent K) P hPK hzP hdP
      (q a') hqa.1 hqa.2 hfix
      ((twoCore_sqtk hsq).stronglyQuasithin 3 Nat.prime_three (by decide)) hzc
  apply (eq_bot_iff_card _).mpr
  rw [← Nat.card_congr (centerCongr ((twoCoreComponentEquiv hkc).trans eq)).toEquiv, hz]
  simp

private theorem ker_eq_twoCore_of_centerless
    {X Y : Type*} [Group X] [Group Y] [Nontrivial Y]
    [IsQuasisimple (X ⧸ pCore 2 X)]
    (f : X →* Y) (hf : Function.Surjective f)
    (hc : pCore 2 X ≤ f.ker) (hz : center (X ⧸ pCore 2 X) = ⊥) :
    f.ker = pCore 2 X := by
  apply le_antisymm ?_ hc
  have hk := f.map_ker_central_of_quasisimple_pCore hf hc
  intro x hx
  apply (QuotientGroup.eq_one_iff _).mp
  exact mem_bot.mp (hz ▸ hk (mem_map_of_mem (QuotientGroup.mk' (pCore 2 X)) hx))

/-- The original reduced-module action detects the entire two-core quotient. -/
theorem secondary_projection_kernel_of_three_dvd
    (hn : 1 < n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G))
    (hJK : m.second ≤ KZ)
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (hd : 3 ∣ 2 ^ n - 1) :
    (secondaryProjection m KZ (hK.trans (Subgroup.centralizer_le_normalizer _))).ker =
      pCore 2 KZ := by
  let := hquasi
  let : Nontrivial (image m KZ) := (nontrivial_iff_ne_bot _).mpr
    (secondary_image_ne_bot m hn hUN hcore KZ hJK)
  exact ker_eq_twoCore_of_centerless _ (secondaryProjection_surjective m KZ _)
    (secondaryCore_le_projection_kernel m hr KZ _ hnormal)
    (secondary_twoCore_center_eq_bot_of_three_dvd m hn h KZ hK hJK hcomp hquasi hnormal hd)

/-- The secondary two-core quotient identified by the actual action projection. -/
def secondaryImageEquiv_of_three_dvd
    (hn : 1 < n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G))
    (hJK : m.second ≤ KZ)
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (hd : 3 ∣ 2 ^ n - 1) : (KZ ⧸ pCore 2 KZ) ≃* image m KZ :=
  QuotientGroup.liftEquiv (pCore 2 KZ) (secondaryProjection_surjective m KZ _)
    (secondary_projection_kernel_of_three_dvd m hn h hr hUN hcore KZ hK hJK
      hcomp hquasi hnormal hd).symm

@[simp] theorem secondaryImageEquiv_of_three_dvd_apply
    (hn : 1 < n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G))
    (hJK : m.second ≤ KZ)
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (hd : 3 ∣ 2 ^ n - 1) (k : KZ) :
    secondaryImageEquiv_of_three_dvd m hn h hr hUN hcore KZ hK hJK hcomp hquasi hnormal hd
      (QuotientGroup.mk' (pCore 2 KZ) k) =
        secondaryProjection m KZ (hK.trans (Subgroup.centralizer_le_normalizer _)) k := rfl

open ChapterA.Section03.OddPrime.SourceModels

private theorem starMap_kernel_of_centerless
    {H : Type*} [Group H] [Finite H] (K : Subgroup H) [K.Normal]
    [IsQuasisimple (K ⧸ pCore 2 K)]
    (hz : center (K ⧸ pCore 2 K) = ⊥) (hd : 3 ∣ Nat.card K) :
    ((starMap 3 H).subgroupMap K).ker = pCore 2 K := by
  let f := (starMap 3 H).subgroupMap K
  have hne : starComponent 3 K ≠ ⊥ := by
    intro he
    have hle : K ≤ pPrimeCore 3 H := by
      intro k hk
      exact (QuotientGroup.eq_one_iff _).mp
        (mem_bot.mp (he ▸ mem_map_of_mem (starMap 3 H) hk))
    exact (Nat.prime_three.coprime_iff_not_dvd.mp
      (pPrimeCore_coprime_card (p := 3) (G := H))) (hd.trans (card_dvd_of_le hle))
  let : Nontrivial (K.map (starMap 3 H)) := (nontrivial_iff_ne_bot _).mpr hne
  have hcore : pCore 2 K ≤ f.ker := by
    have hc : (pCore 2 K).map K.subtype ≤ pPrimeCore 3 H := by
      apply le_sSup
      refine ⟨inferInstance,?_⟩
      rw [card_map_of_injective K.subtype_injective]
      obtain ⟨d,he⟩ := (pCore_isPGroup (p := 2) (G := K)).exists_card_eq
      rw [he]
      exact (by decide : Nat.Coprime 3 2).pow_right d
    intro k hk
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff _).mpr (hc (mem_map_of_mem K.subtype hk))
  exact ker_eq_twoCore_of_centerless f ((starMap 3 H).subgroupMap_surjective K) hcore hz

/-- The source star map has the same intrinsic kernel on the relative component. -/
theorem secondary_starProjection_kernel_of_three_dvd
    (hn : 1 < n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G))
    (hJK : m.second ≤ KZ)
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (hd : 3 ∣ 2 ^ n - 1) (a : G) (haY : a ∈ rootTorus m) :
    ((starMap 3 (KZ ⊔ zpowers a : Subgroup G)).subgroupMap
      (KZ.subgroupOf (KZ ⊔ zpowers a))).ker = pCore 2 (KZ.subgroupOf (KZ ⊔ zpowers a)) := by
  let E := KZ ⊔ zpowers a
  let K := KZ.subgroupOf E
  have hKN := hK.trans (Subgroup.centralizer_le_normalizer _)
  have hEN : E ≤ m.rootNormalizer := sup_le hKN
    (zpowers_le.mpr (rootTorus_le_normalizer m haY))
  let : K.Normal := normal_subgroupOf_of_le_normalizer (hEN.trans hnormal)
  let e : K ≃* KZ := subgroupOfEquivOfLe (show KZ ≤ E from le_sup_left)
  let eq : (K ⧸ pCore 2 K) ≃* KZ ⧸ pCore 2 KZ :=
    QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  let := hquasi
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv eq.symm
  have hz : center (K ⧸ pCore 2 K) = ⊥ := by
    apply (eq_bot_iff_card _).mpr
    rw [Nat.card_congr (centerCongr eq).toEquiv,
      secondary_twoCore_center_eq_bot_of_three_dvd m hn h KZ hK hJK hcomp hquasi hnormal hd]
    simp
  have hdK : 3 ∣ Nat.card K := by
    rw [Nat.card_congr e.toEquiv]
    exact (m.scalar_prime_dvd_levi hd).trans
      (card_dvd_of_le ((m.leviEmbedding_range_le_second hn).trans hJK))
  exact starMap_kernel_of_centerless K hz hdK

/-- Compare the source star component and faithful actor through their original maps. -/
def secondaryStarEquiv_of_three_dvd
    (hn : 1 < n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G))
    (hJK : m.second ≤ KZ)
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (hd : 3 ∣ 2 ^ n - 1) (a : G) (haY : a ∈ rootTorus m) :
    starComponent 3 (KZ.subgroupOf (KZ ⊔ zpowers a)) ≃* image m KZ := by
  let K := KZ.subgroupOf (KZ ⊔ zpowers a)
  let e : K ≃* KZ := subgroupOfEquivOfLe (show KZ ≤ KZ ⊔ zpowers a from le_sup_left)
  let eq : (K ⧸ pCore 2 K) ≃* KZ ⧸ pCore 2 KZ :=
    QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  let es : (K ⧸ pCore 2 K) ≃* starComponent 3 K :=
    QuotientGroup.liftEquiv (pCore 2 K)
      ((starMap 3 (KZ ⊔ zpowers a : Subgroup G)).subgroupMap_surjective K)
      (secondary_starProjection_kernel_of_three_dvd m hn h KZ hK hJK hcomp hquasi hnormal hd a haY).symm
  exact es.symm.trans (eq.trans
    (secondaryImageEquiv_of_three_dvd m hn h hr hUN hcore KZ hK hJK hcomp hquasi hnormal hd))

@[simp] theorem secondaryStarEquiv_of_three_dvd_apply
    (hn : 1 < n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G))
    (hJK : m.second ≤ KZ)
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (hd : 3 ∣ 2 ^ n - 1) (a : G) (haY : a ∈ rootTorus m)
    (k : KZ.subgroupOf (KZ ⊔ zpowers a)) :
    secondaryStarEquiv_of_three_dvd m hn h hr hUN hcore KZ hK hJK hcomp hquasi hnormal hd a haY
      ((starMap 3 (KZ ⊔ zpowers a : Subgroup G)).subgroupMap (KZ.subgroupOf (KZ ⊔ zpowers a)) k) =
        secondaryProjection m KZ (hK.trans (Subgroup.centralizer_le_normalizer _))
          (subgroupOfEquivOfLe (show KZ ≤ KZ ⊔ zpowers a from le_sup_left) k) := by
  let K := KZ.subgroupOf (KZ ⊔ zpowers a)
  let e : K ≃* KZ := subgroupOfEquivOfLe (show KZ ≤ KZ ⊔ zpowers a from le_sup_left)
  let eq : (K ⧸ pCore 2 K) ≃* KZ ⧸ pCore 2 KZ :=
    QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  let es : (K ⧸ pCore 2 K) ≃* starComponent 3 K :=
    QuotientGroup.liftEquiv (pCore 2 K)
      ((starMap 3 (KZ ⊔ zpowers a : Subgroup G)).subgroupMap_surjective K)
      (secondary_starProjection_kernel_of_three_dvd m hn h KZ hK hJK hcomp hquasi hnormal hd a haY).symm
  change (secondaryImageEquiv_of_three_dvd m hn h hr hUN hcore KZ hK hJK hcomp hquasi hnormal hd)
    (eq (es.symm (es (QuotientGroup.mk' (pCore 2 K) k)))) = _
  rw [es.symm_apply_apply]
  rfl

open Chapter1.Section02.LocalModels in
theorem secondary_image_projective_of_cartan_alternative
    (hn : 1 < n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G))
    (hJK : m.second ≤ KZ)
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (hd : 3 ∣ 2 ^ n - 1) (a : G) (haY : a ∈ rootTorus m)
    (halt : ProjectiveAlternative 3 (KZ.subgroupOf (KZ ⊔ zpowers a))) :
    ∃ (unitary : Bool) (q : ℕ), SignedCongruence unitary q ∧
      IsPSLSign (image m KZ) unitary 3 q := by
  obtain ⟨_,u,q,hq,hm,_⟩ := halt
  let e := secondaryStarEquiv_of_three_dvd m hn h hr hUN hcore KZ hK hJK hcomp hquasi hnormal hd a haY
  refine ⟨u,q,hq,?_⟩
  cases u with
  | false => exact hm.of_mulEquiv e.symm
  | true => exact hm.of_mulEquiv e.symm

/-- Odd ranks survive the exact two-core action kernel. -/
theorem secondary_image_oddRank_eq_of_three_dvd
    (hn : 1 < n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G))
    (hJK : m.second ≤ KZ)
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (hd : 3 ∣ 2 ^ n - 1) (p : ℕ) (hp : p.Prime) (ho : Odd p) :
    primeRank p (image m KZ) = primeRank p KZ := by
  let : Fact p.Prime := ⟨hp⟩
  rw [← primeRank_congr p
    (secondaryImageEquiv_of_three_dvd m hn h hr hUN hcore KZ hK hJK hcomp hquasi hnormal hd)]
  exact primeRank_quotient_eq_of_isTwoGroup p ho _ pCore_isPGroup

open Chapter1.Section02.LocalModels in
/-- The surviving high-rank alternative now describes the actual faithful
FF actor, with its original rank and no lost central cover. -/
theorem secondary_image_projective_of_high_three_rank
    (hn : 1 < n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G))
    (hJK : m.second ≤ KZ)
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (hd : 3 ∣ 2 ^ n - 1) (hhigh : 1 < primeRank 3 KZ) :
    center (image m KZ) = ⊥ ∧ 1 < primeRank 3 (image m KZ) ∧
      ∃ (unitary : Bool) (q : ℕ), SignedCongruence unitary q ∧
        IsPSLSign (image m KZ) unitary 3 q := by
  obtain ⟨a,haY,_,_,halt⟩ := projective_alternative_of_high_rank m hn h KZ hK hJK
    hcomp hquasi hnormal 3 Nat.prime_three (by decide) hd hhigh
  refine ⟨?_,?_,secondary_image_projective_of_cartan_alternative m hn h hr hUN hcore
    KZ hK hJK hcomp hquasi hnormal hd a haY halt⟩
  · apply (eq_bot_iff_card _).mpr
    rw [← Nat.card_congr (centerCongr
      (secondaryImageEquiv_of_three_dvd m hn h hr hUN hcore KZ hK hJK hcomp hquasi hnormal hd)).toEquiv,
      secondary_twoCore_center_eq_bot_of_three_dvd m hn h KZ hK hJK hcomp hquasi hnormal hd]
    simp
  · rwa [secondary_image_oddRank_eq_of_three_dvd m hn h hr hUN hcore KZ hK hJK
      hcomp hquasi hnormal hd 3 Nat.prime_three (by decide)]

private theorem binary_linearThree_rank_le_one_of_centerless
    (F : ChapterB.QuasisimpleSource.BinaryField)
    (hz : center (Matrix.SpecialLinearGroup (Fin 3) F.Carrier) = ⊥) :
    primeRank 3 (Matrix.SpecialLinearGroup (Fin 3) F.Carrier) ≤ 1 := by
  have ho : Odd F.degree := by
    apply Nat.not_even_iff_odd.mp
    intro he
    have hh := (Matrix.SL3.center_eq_bot_iff_card_mod_three F.Carrier).mp hz
    rw [F.card_eq, Nat.BinaryTorusParity.two_pow_mod_three,
      if_pos (Nat.even_iff.mp he)] at hh
    exact hh rfl
  rw [primeRank_equiv 3 (Matrix.SL3.equivProjectiveOfCenterEqBot F.Carrier hz)]
  exact Matrix.PSL3.BinaryCubicRankParity.rank_le_one_of_odd F.card_eq ho

/-- In the high-three-rank branch, neither a natural nor a doubled-natural
binary SL₃ marking can describe the original secondary image. -/
theorem secondary_image_not_linearThree_of_high_three_rank
    (hn : 1 < n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G))
    (hJK : m.second ≤ KZ)
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (hd : 3 ∣ 2 ^ n - 1) (hhigh : 1 < primeRank 3 KZ)
    (F : ChapterB.QuasisimpleSource.BinaryField)
    (e : image m KZ ≃* Matrix.SpecialLinearGroup (Fin 3) F.Carrier) : False := by
  have hz : center (Matrix.SpecialLinearGroup (Fin 3) F.Carrier) = ⊥ := by
    apply (eq_bot_iff_card _).mpr
    rw [← Nat.card_congr (centerCongr
      ((secondaryImageEquiv_of_three_dvd m hn h hr hUN hcore KZ hK hJK hcomp hquasi hnormal hd).trans e)).toEquiv,
      secondary_twoCore_center_eq_bot_of_three_dvd m hn h KZ hK hJK hcomp hquasi hnormal hd]
    simp
  have hb := binary_linearThree_rank_le_one_of_centerless F hz
  rw [← primeRank_congr 3 e, secondary_image_oddRank_eq_of_three_dvd m hn h hr hUN hcore KZ hK hJK
    hcomp hquasi hnormal hd 3 Nat.prime_three (by decide)] at hb
  omega

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootFF
