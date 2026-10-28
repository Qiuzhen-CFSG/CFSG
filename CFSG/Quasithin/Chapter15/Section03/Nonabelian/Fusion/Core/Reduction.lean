module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Constructions
public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Theory.GroupTheory.PGroup.Omega
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.ResidualCentralLayerSplitting
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PGroup.ExtraspecialCentralizer
public import Theory.ElementaryAbelian.ExtraspecialEquiv
public import Theory.GroupTheory.EmbeddedCenterMap
public import Theory.ThreeSubgroups
public import Theory.GroupTheory.TwoLayerCentralizer
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# The local centralizer argument for 15.3.59

The literal kernel of the H-action on U/Z and extraspecial commutator duality
first give Q_H = U C_T(U). The three-subgroups lemma and two-perfectness
then show that K centralizes C_T(U), provided K = [K,V]. Once the residual
Sylow group lies in YU with the source order bound, its image is a full
Sylow subgroup of YU. Coprime splitting of C_T(U)V leaves a T-normal fixed
factor disjoint from V; the omega-center condition forces this factor to be
trivial. These arguments prove U = Q_H and the Sylow conclusion from the
remaining explicit residual calculations.

The final index transport and residual supplement retain the actual subgroup
embeddings. The latter includes an elementwise product factorization. None
of these reductions supplies the marked L₃(2) residual/Frattini calculation,
the full natural/dual recognition, or the two-layer automizer calculation
O²(M) = Y. The assembly owner must discharge them before asserting 15.3.59.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.1149–1150; earlier local inputs are on pp.1142 and 1145–1148.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core
open Subgroup
open CFSG.Quasithin.Chapter15.Section03.Nonabelian

variable {G : Type*} [Group G] [Finite G]

/-- The source omega-center, embedded through the two actual subtype maps. -/
def omegaCenterAmbient (T : Subgroup G) : Subgroup G :=
  ((omega₁ (center T) (p := 2)).map (center T).subtype).map T.subtype

private theorem normal_disjoint_omega_eq_bot (T C V : Subgroup G)
    (hT : IsPGroup 2 T) (hCT : C ≤ T)
    (hTC : T ≤ normalizer (C : Set G))
    (hΩ : omegaCenterAmbient T ≤ V) (hd : Disjoint C V) : C = ⊥ := by
  let D := C.subgroupOf T
  let : D.Normal := normal_subgroupOf_of_le_normalizer hTC
  let : Fact (IsPGroup 2 T) := ⟨hT⟩
  by_contra hn
  have hD : D ≠ ⊥ := by
    intro he
    have hm := congrArg (map T.subtype) he
    rw [map_subgroupOf_eq_of_le hCT, Subgroup.map_bot] at hm
    exact hn hm
  let : Nontrivial D := (nontrivial_iff_ne_bot D).mpr hD
  obtain ⟨A, _, hAD, hA, hAc⟩ :=
    exists_central_subgroup_card_eq_prime_in_normal (p := 2) D inferInstance
  have hAbot : A = ⊥ := by
    apply eq_bot_iff.mpr
    intro a ha
    have haC : (a : G) ∈ C := hAD ha
    have haΩ : (a : G) ∈ omegaCenterAmbient T := by
      apply mem_map_of_mem
      apply mem_map_of_mem (center T).subtype (x := ⟨a, hAc ha⟩)
      apply Subgroup.subset_closure
      change (⟨a, hAc ha⟩ : center T) ^ (2 ^ 1) = 1
      apply Subtype.ext
      have hp := congrArg (fun x : A => (x : T)) (pow_card_eq_one' (x := ⟨a, ha⟩))
      change a ^ Nat.card A = 1 at hp
      change a ^ (2 ^ 1) = 1
      simpa only [hA, pow_one] using hp
    have habot : (a : G) ∈ (⊥ : Subgroup G) := (disjoint_iff.mp hd).le ⟨haC, hΩ haΩ⟩
    exact Subtype.ext (mem_bot.mp habot)
  have hc : Nat.card A = 1 := by simp [hAbot]
  omega

omit [Finite G] in
open scoped Pointwise in
private theorem centralizer_join (I C P : Subgroup G)
    (hCI : C ≤ normalizer (I : Set G))
    (hCP : C ≤ centralizer (P : Set G)) :
    (I ⊔ C) ⊓ centralizer (P : Set G) =
      (I ⊓ centralizer (P : Set G)) ⊔ C := by
  apply le_antisymm
  · intro x hx
    have hf : x ∈ (I : Set G) * (C : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left I C hCI]
      exact hx.1
    obtain ⟨i, hi, c, hc, rfl⟩ := hf
    have hip : i ∈ centralizer (P : Set G) := by
      have he := (centralizer (P : Set G)).mul_mem hx.2
        ((centralizer (P : Set G)).inv_mem (hCP hc))
      simpa only [mul_inv_cancel_right] using he
    exact mul_mem_sup ⟨hi, hip⟩ hc
  · exact sup_le (inf_le_inf le_sup_left le_rfl) (le_inf le_sup_right hCP)

private theorem centralizer_layer_collapse (T I P Y Q V C : Subgroup G)
    (hT : IsPGroup 2 T) (hCT : C ≤ T) (hVT : V ≤ T)
    (hVI : V ≤ I) (hYI : Y ≤ I)
    (hCI : C ≤ normalizer (I : Set G))
    (hCP : C ≤ centralizer (P : Set G))
    (hYP : Y ≤ normalizer (P : Set G))
    (hIP : I ⊓ centralizer (P : Set G) = V)
    (hQY : Q ≤ Y) (hQ : IsPGroup 2 Q)
    [hQN : (Q.subgroupOf Y).Normal]
    (hodd : Odd (Nat.card (Y ⧸ Q.subgroupOf Y)))
    (hperfect : IsPPerfect 2 Y) (hQP : Q ≤ P)
    (hfix : V ⊓ centralizer (Y : Set G) = ⊥)
    (hTC : T ≤ normalizer (C : Set G))
    (hTV : T ≤ normalizer (V : Set G))
    (hTY : T ≤ normalizer (Y : Set G))
    (hΩ : omegaCenterAmbient T ≤ V) : C ≤ V := by
  let B := V ⊔ C
  have hBT : B ≤ T := sup_le hVT hCT
  have hBP : B ≤ centralizer (P : Set G) :=
    sup_le (hIP ▸ inf_le_right) hCP
  have hB : (I ⊔ C) ⊓ centralizer (P : Set G) = B := by
    rw [centralizer_join I C P hCI hCP, hIP]
  have hYB : Y ≤ normalizer (B : Set G) := by
    rw [← hB]
    exact (le_inf ((hYI.trans le_sup_left).trans (I ⊔ C).le_normalizer)
      (hYP.trans (normalizer_le_normalizer_centralizer P))).trans
        inf_normalizer_le_normalizer_inf
  have hBI : B ≤ normalizer (I : Set G) := sup_le (hVI.trans I.le_normalizer) hCI
  have hcommB : ⁅B, Y⁆ ≤ B := le_normalizer_iff_commutator_le_left.mp hYB
  have hcommI : ⁅B, Y⁆ ≤ I :=
    (commutator_mono le_rfl hYI).trans (le_normalizer_iff_commutator_le_right.mp hBI)
  have hcomm : ⁅B, Y⁆ ≤ V := by
    rw [← hIP]
    exact le_inf hcommI (hcommB.trans hBP)
  have hcommQ : ⁅B, Q⁆ ≤ (⊥ : Subgroup G) := by
    rw [le_bot_iff, commutator_eq_bot_iff_le_centralizer]
    exact hBP.trans (centralizer_le hQP)
  have hsplit := eq_sup_centralizer_of_no_two_quotient_central_layer_of_isPGroup
    Y Q B V ⊥ hQY hQ (hT.to_subgroup (B.subgroupOf T) |>.of_equiv
      (subgroupOfEquivOfLe hBT)) hodd hperfect hYB le_sup_left bot_le bot_le
        hcomm hcommQ
  let D := B ⊓ centralizer (Y : Set G)
  have hTD : T ≤ normalizer (D : Set G) :=
    (le_inf ((le_inf hTV hTC).trans
      (normalizer_inf_normalizer_le_normalizer_sup V C))
      (hTY.trans (normalizer_le_normalizer_centralizer Y))).trans
        inf_normalizer_le_normalizer_inf
  have hd : Disjoint D V := disjoint_iff.mpr (by
    apply eq_bot_iff.mpr
    intro d hd
    exact hfix.le ⟨hd.2, hd.1.2⟩)
  have hD := normal_disjoint_omega_eq_bot T D V hT
    (inf_le_left.trans hBT) hTD hΩ hd
  have he : B = V := by
    change B = V ⊔ D at hsplit
    simpa only [hD, sup_bot_eq] using hsplit
  exact (le_sup_right : C ≤ B).trans he.le

private theorem sylow_of_lower_bound (T L : Subgroup G) (n : ℕ)
    (hT : IsPGroup 2 T) (hTL : T ≤ L)
    (hlower : 2 ^ n ≤ Nat.card T)
    (hpart : 2 ^ (Nat.card L).factorization 2 = 2 ^ n) :
    ∃ S : Sylow 2 L, (S : Subgroup L).map L.subtype = T := by
  obtain ⟨S, hS⟩ := (hT.comap_subtype : IsPGroup 2 (T.subgroupOf L)).exists_le_sylow
  have hcard : Nat.card S ≤ Nat.card (T.subgroupOf L) := by
    rw [S.card_eq_multiplicity, hpart,
      Nat.card_congr (subgroupOfEquivOfLe hTL).toEquiv]
    exact hlower
  have he := eq_of_le_of_card_ge hS hcard
  refine ⟨S, ?_⟩
  rw [← he]
  exact map_subgroupOf_eq_of_le hTL

private theorem extraspecial_core_split (U Q T : Subgroup G)
    [IsExtraspecial 2 U] (hUQ : U ≤ Q) (hQT : Q ≤ T)
    (hcomm : ⁅Q, U⁆ ≤ (center U).map U.subtype)
    (hCQ : T ⊓ centralizer (U : Set G) ≤ Q) :
    Q = U ⊔ (T ⊓ centralizer (U : Set G)) := by
  let E := U.subgroupOf Q
  let : IsExtraspecial 2 E := IsExtraspecial.of_mulEquiv
    (subgroupOfEquivOfLe hUQ).symm inferInstance
  have hc : ⁅(⊤ : Subgroup Q), E⁆ ≤ (center E).map E.subtype := by
    apply (map_le_map_iff_of_injective Q.subtype_injective).mp
    rw [map_commutator, ← MonoidHom.range_eq_map, range_subtype,
      map_embeddedCenter E Q.subtype Q.subtype_injective,
      map_subgroupOf_eq_of_le hUQ]
    exact hcomm
  have hgen := congrArg (map Q.subtype) (sup_centralizer_eq_top_of_extraspecial_two E hc)
  rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hUQ,
    ← MonoidHom.range_eq_map, range_subtype] at hgen
  apply le_antisymm
  · rw [← hgen]
    apply sup_le_sup_left
    rintro _ ⟨q, hq, rfl⟩
    refine ⟨hQT q.property, ?_⟩
    intro u hu
    exact congrArg Subtype.val (hq ⟨u, hUQ hu⟩ hu)
  · exact sup_le hUQ hCQ

private theorem residual_centralizer (K C V Z : Subgroup G)
    (hK : IsPPerfect 2 K) (hZ : IsPGroup 2 Z)
    (hgen : ⁅K, V⁆ = K) (hKC : K ≤ normalizer (C : Set G))
    (hKZ : K ≤ centralizer (Z : Set G))
    (hVZ : V ≤ normalizer (Z : Set G))
    (hCZ : C ≤ normalizer (Z : Set G))
    (hCV : ⁅C, V⁆ ≤ Z) : K ≤ centralizer (C : Set G) := by
  have hZK : ⁅Z, K⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hKZ)
  have hrot₁ : ⁅⁅V, C⁆, K⁆ ≤ Z := by
    rw [commutator_comm V C]
    exact (commutator_mono hCV le_rfl).trans (hZK.le.trans bot_le)
  have hrot₂ : ⁅⁅C, K⁆, V⁆ ≤ Z :=
    (commutator_mono (le_normalizer_iff_commutator_le_left.mp hKC) le_rfl).trans hCV
  have hc : ⁅K, C⁆ ≤ Z := by
    rw [← hgen]
    exact commutator_commutator_le_of_rotate_of_le_normalizer
      (hKZ.trans (Subgroup.centralizer_le_normalizer _)) hVZ hCZ hrot₁ hrot₂
  have hr := residual_centralizes_of_two_layer K C Z hZ hKZ hc
  rwa [(pResidual_eq_top_iff 2 K).mpr hK, ← MonoidHom.range_eq_map, range_subtype] at hr

/-- The auxiliary subgroup Q_C = C_T(U) in the proof of 15.3.59. -/
noncomputable def centralizerC (T Z ZS : Subgroup G) : Subgroup G :=
  T ⊓ centralizer (closureU Z ZS : Set G)

omit [Finite G] in
/-- T normalizes Q_C because T normalizes U. -/
theorem centralizerC_normalized (T Z ZS : Subgroup G)
    (hTH : T ≤ centralizerH Z) :
    T ≤ normalizer (centralizerC T Z ZS : Set G) :=
  (le_inf T.le_normalizer ((hTH.trans (H_normalizes_closureU Z ZS)).trans
    (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf

omit [Finite G] in
/-- The literal quotient-action kernel puts C_T(U) in the two-core. -/
theorem centralizerC_le_coreQ (T Z ZS : Subgroup G)
    [(Z.subgroupOf (closureU Z ZS)).Normal]
    (hTH : T ≤ centralizerH Z)
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z)) :
    centralizerC T Z ZS ≤ coreQ Z := by
  intro c hc
  let cH : centralizerH Z := ⟨c, hTH hc.1⟩
  have hker : cH ∈ (quotientAction Z ZS).ker := by
    apply MonoidHom.mem_ker.mpr
    ext v
    induction v using QuotientGroup.induction_on with
    | H u =>
      change quotientAction Z ZS cH (QuotientGroup.mk' _ u) = QuotientGroup.mk' _ u
      rw [quotientAction_mk]
      change QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS)) _ =
        QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS)) u
      apply congrArg
      apply Subtype.ext
      change c * (u : G) * c⁻¹ = (u : G)
      have he := hc.2 (u : G) u.property
      rw [← he, mul_inv_cancel_right]
  exact mem_map_of_mem (centralizerH Z).subtype (hkernel ▸ hker)

omit [Finite G] in
/-- The action-kernel equality of 15.3.48 makes [Q_H,U] central in U. -/
theorem coreQ_commutator_le_Z (Z ZS : Subgroup G)
    [(Z.subgroupOf (closureU Z ZS)).Normal]
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z)) :
    ⁅coreQ Z, closureU Z ZS⁆ ≤ Z := by
  apply commutator_le.mpr
  intro c hc u hu
  obtain ⟨cH, hcH, rfl⟩ := hc
  have hk : quotientAction Z ZS cH = 1 :=
    MonoidHom.mem_ker.mp (hkernel.symm ▸ hcH)
  let uU : closureU Z ZS := ⟨u, hu⟩
  let cu : closureU Z ZS :=
    ⟨(cH : G) * u * (cH : G)⁻¹,
      (mem_normalizer_iff.mp (H_normalizes_closureU Z ZS cH.property) u).mp hu⟩
  have he : QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS)) cu =
      QuotientGroup.mk' _ uU := by
    calc
      _ = quotientAction Z ZS cH (QuotientGroup.mk' _ uU) :=
        (quotientAction_mk Z ZS cH uU).symm
      _ = _ := by rw [hk]; rfl
  have hq : QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS)) (cu * uU⁻¹) = 1 := by
    rw [map_mul, map_inv, he, mul_inv_cancel]
  have hm : cu * uU⁻¹ ∈ Z.subgroupOf (closureU Z ZS) :=
    (QuotientGroup.eq_one_iff _).mp hq
  exact hm

/-- Extraspecial commutator duality gives Q_H = U C_T(U), expressed as a join. -/
theorem coreQ_split (T Z ZS : Subgroup G)
    [(Z.subgroupOf (closureU Z ZS)).Normal]
    [IsExtraspecial 2 (closureU Z ZS)]
    (hTH : T ≤ centralizerH Z) (hUQ : closureU Z ZS ≤ coreQ Z)
    (hQT : coreQ Z ≤ T)
    (hcenter : (center (closureU Z ZS)).map (closureU Z ZS).subtype = Z)
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z)) :
    coreQ Z = closureU Z ZS ⊔ centralizerC T Z ZS := by
  apply extraspecial_core_split _ _ _ hUQ hQT
  · rw [hcenter]
    exact coreQ_commutator_le_Z Z ZS hkernel
  · exact centralizerC_le_coreQ T Z ZS hTH hkernel

/-- The centralizer bound completes the identification of the two-core. -/
theorem coreQ_eq_closure_of_centralizer_bound (T Z ZS : Subgroup G)
    [(Z.subgroupOf (closureU Z ZS)).Normal]
    [IsExtraspecial 2 (closureU Z ZS)]
    (hTH : T ≤ centralizerH Z) (hUQ : closureU Z ZS ≤ coreQ Z)
    (hQT : coreQ Z ≤ T)
    (hcenter : (center (closureU Z ZS)).map (closureU Z ZS).subtype = Z)
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (hC : centralizerC T Z ZS ≤ Z) : closureU Z ZS = coreQ Z := by
  rw [coreQ_split T Z ZS hTH hUQ hQT hcenter hkernel]
  exact (sup_of_le_left (hC.trans (hcenter.symm.le.trans (map_subtype_le _)))).symm

omit [Finite G] in
/-- The full centralizer in H already lies in T; no ambient normality is assumed. -/
theorem centralizerC_eq_H_centralizer (T Z ZS : Subgroup G)
    [(Z.subgroupOf (closureU Z ZS)).Normal]
    (hTH : T ≤ centralizerH Z) (hQT : coreQ Z ≤ T)
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z)) :
    centralizerC T Z ZS = centralizerH Z ⊓ centralizer (closureU Z ZS : Set G) := by
  apply le_antisymm (inf_le_inf hTH le_rfl)
  exact le_inf ((centralizerC_le_coreQ (centralizerH Z) Z ZS le_rfl hkernel).trans hQT)
    inf_le_right

omit [Finite G] in
/-- Relative H-normality of Q_C, derived from the actual action kernel. -/
theorem H_normalizes_centralizerC (T Z ZS : Subgroup G)
    [(Z.subgroupOf (closureU Z ZS)).Normal]
    (hTH : T ≤ centralizerH Z) (hQT : coreQ Z ≤ T)
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z)) :
    centralizerH Z ≤ normalizer (centralizerC T Z ZS : Set G) := by
  rw [centralizerC_eq_H_centralizer T Z ZS hTH hQT hkernel]
  exact (le_inf (centralizerH Z).le_normalizer
    ((H_normalizes_closureU Z ZS).trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf

omit [Finite G] in
/-- The first centralizer commutator in the printed proof lands in Z. -/
theorem centralizerC_commutator_V_le_Z (T Z ZS V : Subgroup G)
    [(Z.subgroupOf (closureU Z ZS)).Normal]
    (hTH : T ≤ centralizerH Z) (hQT : coreQ Z ≤ T)
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (hVT : V ≤ T) (hTV : T ≤ normalizer (V : Set G))
    (hVU : V ⊓ centralizer (closureU Z ZS : Set G) = Z) :
    ⁅centralizerC T Z ZS, V⁆ ≤ Z := by
  apply le_trans ?_ hVU.le
  exact le_inf (le_normalizer_iff_commutator_le_right.mp (inf_le_left.trans hTV))
    ((le_normalizer_iff_commutator_le_left.mp
      ((hVT.trans hTH).trans (H_normalizes_centralizerC T Z ZS hTH hQT hkernel))).trans
        inf_le_right)

/-- Identify the source two-residual with the intrinsic quotient-based residual. -/
theorem twoResidualAmbient_eq_pResidual (H : Subgroup G) :
    Stellmacher.twoResidualAmbient H = (pResidual 2 H).map H.subtype := by
  unfold Stellmacher.twoResidualAmbient Stellmacher.twoResidualSubgroup
  congr 1
  unfold pResidual
  congr 1
  ext N
  constructor
  · rintro ⟨hn, n, hi⟩
    let := hn
    exact ⟨hn, IsPGroup.of_card (by simpa only [index_eq_card] using hi)⟩
  · rintro ⟨hn, hp⟩
    let := hn
    obtain ⟨n, hn'⟩ := hp.exists_card_eq
    exact ⟨hn, n, hn'⟩

/-- The actual K = O²(H) has no nontrivial two-group quotient. -/
theorem residualK_isPPerfect (Z : Subgroup G) : IsPPerfect 2 (residualK Z) := by
  rw [show residualK Z = (pResidual 2 (centralizerH Z)).map (centralizerH Z).subtype from
    twoResidualAmbient_eq_pResidual _]
  exact (isPPerfect_pResidual 2).of_surjective
    ((pResidual 2 (centralizerH Z)).equivMapOfInjective (centralizerH Z).subtype
      (centralizerH Z).subtype_injective).toMonoidHom
    ((pResidual 2 (centralizerH Z)).equivMapOfInjective (centralizerH Z).subtype
      (centralizerH Z).subtype_injective).surjective

/-- Three subgroups and residual perfection lift centralization modulo Z.
The commutator generation K = [K,V] remains an explicit local calculation. -/
theorem residualK_centralizes_centralizerC (T Z ZS V : Subgroup G)
    [(Z.subgroupOf (closureU Z ZS)).Normal]
    (hTH : T ≤ centralizerH Z) (hQT : coreQ Z ≤ T)
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (hVT : V ≤ T) (hTV : T ≤ normalizer (V : Set G))
    (hVU : V ⊓ centralizer (closureU Z ZS : Set G) = Z)
    (hZ : IsPGroup 2 Z)
    (hgen : ⁅residualK Z, V⁆ = residualK Z) :
    residualK Z ≤ centralizer (centralizerC T Z ZS : Set G) := by
  have hKH : residualK Z ≤ centralizerH Z := map_subtype_le _
  have hnorm : centralizerH Z ≤ normalizer (Z : Set G) :=
    Subgroup.centralizer_le_normalizer _
  exact residual_centralizer _ _ _ _ (residualK_isPPerfect Z) hZ hgen
    (hKH.trans (H_normalizes_centralizerC T Z ZS hTH hQT hkernel)) hKH
    ((hVT.trans hTH).trans hnorm) ((inf_le_left.trans hTH).trans hnorm)
    (centralizerC_commutator_V_le_Z T Z ZS V hTH hQT hkernel hVT hTV hVU)

open scoped Pointwise in
/-- Once O²(M) = Y is proved, the Sylow supplement gives M = YT,
including an actual factorization of every element. -/
theorem supplement_of_residual (M Y T : Subgroup G)
    (S : Sylow 2 M) (hS : (S : Subgroup M).map M.subtype = T)
    (hY : Stellmacher.twoResidualAmbient M = Y)
    (hTY : T ≤ normalizer (Y : Set G)) :
    M = Y ⊔ T ∧ (M : Set G) = (Y : Set G) * (T : Set G) ∧
      ∀ m ∈ M, ∃ y ∈ Y, ∃ t ∈ T, m = y * t := by
  have he := congrArg (map M.subtype) (pResidual_sup_sylow_eq_top S)
  rw [Subgroup.map_sup, hS, ← twoResidualAmbient_eq_pResidual M, hY,
    ← MonoidHom.range_eq_map, range_subtype] at he
  have hset : (M : Set G) = (Y : Set G) * (T : Set G) := by
    rw [← he]
    exact coe_mul_of_right_le_normalizer_left Y T hTY
  refine ⟨he.symm, hset, ?_⟩
  intro m hm
  have hm' : m ∈ (Y : Set G) * (T : Set G) := by rw [← hset]; exact hm
  obtain ⟨y, hy, t, ht, hyt⟩ := hm'
  exact ⟨y, hy, t, ht, hyt.symm⟩

omit [Finite G] in
/-- The embedded two-core lies in the actual image of any Sylow two-subgroup. -/
theorem core_le_sylow_image (L : Subgroup G) (S : Sylow 2 L) :
    Stellmacher.twoCoreAmbient L ≤ (S : Subgroup L).map L.subtype :=
  map_mono (pCore_isPGroup.le_sylow_of_normal S)

/-- The residual containment and the matching two-part construct the required
Sylow subgroup, with its ambient image exactly T_K. -/
theorem residualSylow_sylow (T Z ZS Y : Subgroup G)
    (hT : IsPGroup 2 T)
    (hcontain : residualSylow T Z ≤ Y ⊔ closureU Z ZS)
    (hlower : 2 ^ 10 ≤ Nat.card (residualSylow T Z))
    (hpart : 2 ^ (Nat.card (Y ⊔ closureU Z ZS : Subgroup G)).factorization 2 = 2 ^ 10) :
    ∃ S : Sylow 2 (Y ⊔ closureU Z ZS : Subgroup G),
      (S : Subgroup (Y ⊔ closureU Z ZS : Subgroup G)).map (Y ⊔ closureU Z ZS).subtype =
        residualSylow T Z := by
  have hp : IsPGroup 2 (residualSylow T Z) :=
    (hT.to_subgroup ((residualSylow T Z).subgroupOf T)).of_equiv
      (subgroupOfEquivOfLe inf_le_left)
  exact sylow_of_lower_bound _ _ 10 hp hcontain hlower hpart

/-- Coprime splitting of Q_C V and the omega-center condition eliminate Q_C/Z.
The input P ≤ T_K is supplied by the preceding Sylow construction. -/
theorem centralizerC_le_Z_of_residual_action (T Z ZS V Y : Subgroup G)
    [(Z.subgroupOf (closureU Z ZS)).Normal]
    (hT : IsPGroup 2 T) (hTH : T ≤ centralizerH Z) (hQT : coreQ Z ≤ T)
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (hVT : V ≤ T) (hTV : T ≤ normalizer (V : Set G))
    (hTY : T ≤ normalizer (Y : Set G)) (hVY : V ≤ Y)
    (hVU : V ⊓ centralizer (closureU Z ZS : Set G) = Z)
    (hZ : IsPGroup 2 Z) (hΩ : omegaCenterAmbient T ≤ V)
    (hgen : ⁅residualK Z, V⁆ = residualK Z)
    (hP : Stellmacher.twoCoreAmbient (Y ⊔ closureU Z ZS) ≤ residualSylow T Z)
    (hYP : Y ≤ normalizer (Stellmacher.twoCoreAmbient (Y ⊔ closureU Z ZS) : Set G))
    (hIP : (Y ⊔ closureU Z ZS) ⊓
      centralizer (Stellmacher.twoCoreAmbient (Y ⊔ closureU Z ZS) : Set G) = V)
    (hQY : (Stellmacher.twoCoreAmbient Y).subgroupOf Y |>.Normal)
    (hodd : let _ := hQY
      Odd (Nat.card (Y ⧸ (Stellmacher.twoCoreAmbient Y).subgroupOf Y)))
    (hperfect : IsPPerfect 2 Y)
    (hQYP : Stellmacher.twoCoreAmbient Y ≤ Stellmacher.twoCoreAmbient (Y ⊔ closureU Z ZS))
    (hfix : V ⊓ centralizer (Y : Set G) = ⊥) :
    centralizerC T Z ZS ≤ Z := by
  let _ := hQY
  have hCK := le_centralizer_iff.mp
    (residualK_centralizes_centralizerC T Z ZS V hTH hQT hkernel hVT hTV hVU hZ hgen)
  have hCP : centralizerC T Z ZS ≤
      centralizer (Stellmacher.twoCoreAmbient (Y ⊔ closureU Z ZS) : Set G) :=
    hCK.trans (centralizer_le (hP.trans inf_le_right))
  have hCI : centralizerC T Z ZS ≤ normalizer ((Y ⊔ closureU Z ZS : Subgroup G) : Set G) :=
    (le_inf (inf_le_left.trans hTY)
      ((inf_le_left.trans hTH).trans (H_normalizes_closureU Z ZS))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hCV := centralizer_layer_collapse T (Y ⊔ closureU Z ZS)
    (Stellmacher.twoCoreAmbient (Y ⊔ closureU Z ZS)) Y (Stellmacher.twoCoreAmbient Y)
    V (centralizerC T Z ZS) hT inf_le_left hVT (hVY.trans le_sup_left) le_sup_left
    hCI hCP hYP hIP (map_subtype_le _) (pCore_isPGroup.map _) hodd hperfect hQYP hfix
    (centralizerC_normalized T Z ZS hTH) hTV hTY hΩ
  exact (le_inf hCV inf_le_right).trans hVU.le

omit [Finite G] in
open scoped Pointwise in
/-- Convert the residual join description into its set product and element factors.
This is a factorization helper; it does not prove the input join equality. -/
theorem residualSylow_product_of_join (T Z ZS V : Subgroup G)
    (hTH : T ≤ centralizerH Z)
    (hjoin : residualSylow T Z = closureU Z ZS ⊔ (T ⊓ centralizer (V : Set G))) :
    (residualSylow T Z : Set G) =
      (closureU Z ZS : Set G) * (T ⊓ centralizer (V : Set G) : Subgroup G) ∧
      ∀ k ∈ residualSylow T Z,
        ∃ u ∈ closureU Z ZS, ∃ c ∈ T ⊓ centralizer (V : Set G), k = u * c := by
  have hn : T ⊓ centralizer (V : Set G) ≤ normalizer (closureU Z ZS : Set G) :=
    (inf_le_left.trans hTH).trans (H_normalizes_closureU Z ZS)
  have hs : (residualSylow T Z : Set G) =
      (closureU Z ZS : Set G) * (T ⊓ centralizer (V : Set G) : Subgroup G) := by
    rw [hjoin]
    exact coe_mul_of_right_le_normalizer_left _ _ hn
  refine ⟨hs, ?_⟩
  intro k hk
  have hk' : k ∈ (closureU Z ZS : Set G) * (T ⊓ centralizer (V : Set G) : Subgroup G) := by
    rw [← hs]; exact hk
  obtain ⟨u, hu, c, hc, huc⟩ := hk'
  exact ⟨u, hu, c, hc, huc.symm⟩

/-- Transport the Sylow-relative residual index to the intrinsic quotient of H. -/
theorem residualSylow_index (T Z : Subgroup G) (S : Sylow 2 (centralizerH Z))
    (hS : (S : Subgroup (centralizerH Z)).map (centralizerH Z).subtype = T) :
    ((residualSylow T Z).subgroupOf T).index = (pResidual 2 (centralizerH Z)).index := by
  change (T ⊓ residualK Z).relIndex T = _
  rw [inf_relIndex_left]
  change (Stellmacher.twoResidualAmbient (centralizerH Z)).relIndex T = _
  rw [twoResidualAmbient_eq_pResidual, ← hS,
    relIndex_map_map_of_injective _ _ (centralizerH Z).subtype_injective]
  rw [← relIndex_sup_left (S : Subgroup (centralizerH Z)),
    pResidual_sup_sylow_eq_top S, relIndex_top_right]

/-- Earlier local consequences used by the centralizer calculation.
These are scalar, normality and fixed-point conclusions through 15.3.58,
not a replacement for its recognition and natural/dual action. In particular
this record contains none of the four conclusions of 15.3.59. -/
structure LocalCoreData (T Z ZS V Y : Subgroup G)
    [(Z.subgroupOf (closureU Z ZS)).Normal] : Prop where
  two_group : IsPGroup 2 T
  T_le_H : T ≤ centralizerH Z
  closure_le_core : closureU Z ZS ≤ coreQ Z
  core_le_sylow : coreQ Z ≤ T
  center_closure : (center (closureU Z ZS)).map (closureU Z ZS).subtype = Z
  action_kernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z)
  module_le_sylow : V ≤ T
  normalizes_module : T ≤ normalizer (V : Set G)
  normalizes_Y : T ≤ normalizer (Y : Set G)
  module_le_Y : V ≤ Y
  module_centralizer : V ⊓ centralizer (closureU Z ZS : Set G) = Z
  center_two_group : IsPGroup 2 Z
  omega_le_module : omegaCenterAmbient T ≤ V
  normalizes_pair_core : Y ≤ normalizer
    (Stellmacher.twoCoreAmbient (Y ⊔ closureU Z ZS) : Set G)
  pair_core_centralizer : (Y ⊔ closureU Z ZS) ⊓
    centralizer (Stellmacher.twoCoreAmbient (Y ⊔ closureU Z ZS) : Set G) = V
  Y_core_normal : ((Stellmacher.twoCoreAmbient Y).subgroupOf Y).Normal
  Y_quotient_odd : let _ := Y_core_normal
    Odd (Nat.card (Y ⧸ (Stellmacher.twoCoreAmbient Y).subgroupOf Y))
  Y_perfect : IsPPerfect 2 Y
  Y_core_le_pair_core : Stellmacher.twoCoreAmbient Y ≤
    Stellmacher.twoCoreAmbient (Y ⊔ closureU Z ZS)
  module_fixed : V ⊓ centralizer (Y : Set G) = ⊥
  pair_two_part : 2 ^ (Nat.card (Y ⊔ closureU Z ZS : Subgroup G)).factorization 2 = 2 ^ 10

/-- Assemble 15.3.59(1–2) from the remaining residual generation and size
calculations. This remains conditional until those three premises and the
earlier local data are supplied from the genuine recognized action. -/
theorem core_and_sylow_of_local_calculations (T Z ZS V Y : Subgroup G)
    [(Z.subgroupOf (closureU Z ZS)).Normal] [IsExtraspecial 2 (closureU Z ZS)]
    (d : LocalCoreData T Z ZS V Y)
    (hgen : ⁅residualK Z, V⁆ = residualK Z)
    (hcontain : residualSylow T Z ≤ Y ⊔ closureU Z ZS)
    (hlower : 2 ^ 10 ≤ Nat.card (residualSylow T Z)) :
    closureU Z ZS = coreQ Z ∧
      ∃ S : Sylow 2 (Y ⊔ closureU Z ZS : Subgroup G),
        (S : Subgroup (Y ⊔ closureU Z ZS : Subgroup G)).map (Y ⊔ closureU Z ZS).subtype =
          residualSylow T Z := by
  obtain ⟨S, hS⟩ := residualSylow_sylow T Z ZS Y d.two_group hcontain hlower d.pair_two_part
  have hP := (core_le_sylow_image _ S).trans hS.le
  have hC := centralizerC_le_Z_of_residual_action T Z ZS V Y d.two_group d.T_le_H
    d.core_le_sylow d.action_kernel d.module_le_sylow d.normalizes_module
    d.normalizes_Y d.module_le_Y d.module_centralizer d.center_two_group
    d.omega_le_module hgen hP d.normalizes_pair_core d.pair_core_centralizer
    d.Y_core_normal d.Y_quotient_odd d.Y_perfect d.Y_core_le_pair_core d.module_fixed
  exact ⟨coreQ_eq_closure_of_centralizer_bound T Z ZS d.T_le_H d.closure_le_core
    d.core_le_sylow d.center_closure d.action_kernel hC, S, hS⟩

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core
