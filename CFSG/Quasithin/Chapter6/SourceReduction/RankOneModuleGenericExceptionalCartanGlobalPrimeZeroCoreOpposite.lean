module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeZeroCoreLeftAction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5LocalFactorization
public import Theory.SpecificGroups.PSL2.BinarySylowEmbedding

/-!
# A large left-normal subgroup inside the opposite two-core

For the original zero-core prime pair, suppose the selected right factor
has a binary PSL₂ quotient. Its Borel normalizes the literal sourceS, so
the source Sylow factorization expresses sourceS as the full right two-core
times its intersection with the right factor. That intersection has abelian
image in PSL₂. Consequently the commutator of sourceS lies in the full
right two-core, without assuming sourceS lies in the selected factor.

The derived subgroup N of the full left two-core therefore lies in the
right two-core. The original chosen module gives |N| ≥ 2ⁿ. Characteristic
normality makes N invariant under the whole left parabolic. Faithfulness
and right Borel maximality identify its right-factor normalizer with the
original right Borel. In particular N is strictly smaller than the full
right two-core, whose order is at least 2^(n+1).

These are constraints on the actual two-core intersection for the remaining
mixed F.1.12 recognition. They assume no amalgam model, do not identify the
original degree n with the right degree f, and do not assert exhaustive
recognition. The Chapter12 extension applies them to the same escaping pair.
Source: Aschbacher--Smith 5.2.2, printed pp.647--648, using F.1.3 and F.1.9,
pp.260--262 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

private theorem local_sylow_derived_le_core
    (K S : Subgroup G) (P : Sylow 2 K)
    (hP : (P : Subgroup K).map K.subtype = S ⊓ K)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (K ⧸ pCore 2 K) ≃* PSL(2,F)) :
    ⁅S ⊓ K,S ⊓ K⁆ ≤ K.pCoreIn 2 := by
  let q := QuotientGroup.mk' (pCore 2 K)
  let Q := P.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  let : IsMulCommutative Q :=
    Theory.PSL2.binary_sylow_commutative_of_injective e.toMonoidHom e.injective Q
  have hcomm : ⁅(Q : Subgroup (K ⧸ pCore 2 K)),(Q : Subgroup (K ⧸ pCore 2 K))⁆ = ⊥ :=
    commutator_self_eq_bot_iff.mpr inferInstance
  have hle : ⁅(P : Subgroup K),(P : Subgroup K)⁆ ≤ pCore 2 K := by
    rw [←QuotientGroup.ker_mk' (pCore 2 K),←Subgroup.map_eq_bot_iff,map_commutator]
    exact hcomm
  have hh := map_mono (f := K.subtype) hle
  rwa [map_commutator,hP] at hh

/-- The actual source Sylow has abelian image modulo the full right core
when the selected factor has a binary linear quotient. -/
theorem LocalData.zeroCore_sylow_derived_le_right_core
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p f : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 = ⊥)
    (hlin : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^f)) :
    ⁅Global.sourceS L H,Global.sourceS L H⁆ ≤ (R ⊔ Global.sourceS L H).pCoreIn 2 := by
  let S := Global.sourceS L H
  let J := R ⊔ S
  let Q := J.pCoreIn 2
  let V := S ⊓ R
  have hf := d.hypothesisF11 h hH c hd hz
  have hSN : ChapterF.Source.borel R S ≤ normalizer (S : Set G) := by
    have hh := hf.commonBorel_normalizes_localSylow 0
    change ChapterF.Source.commonBorel ![D ⊔ S,R] S ≤ normalizer ((S ⊓ (D ⊔ S) : Subgroup G) : Set G) at hh
    rw [inf_eq_left.mpr (show S ≤ D ⊔ S from le_sup_right)] at hh
    exact (ChapterF.Source.borel_le_commonBorel 1).trans hh
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hlin
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  have he : S = Q ⊔ V := hf.linear_local_sylow_factorization 1 F e hSN
  obtain ⟨P,hP⟩ := d.right_sylow
  have hv : ⁅V,V⁆ ≤ Q := (local_sylow_derived_le_core R S P hP e).trans
    (pCoreIn_mono_of_normalizes le_sup_left (sup_le R.le_normalizer d.S_normalizes_right))
  have hn : J ≤ normalizer (Q : Set G) :=
    J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
  have hVJ : V ≤ J := inf_le_right.trans le_sup_left
  have hVS : ⁅V,S⁆ ≤ Q := by
    rw [commutator_comm,he]
    exact commutator_sup_le_of_relative_normal J Q V V Q hn (pCoreIn_le 2 J) hVJ
      (le_normalizer_iff_commutator_le_left.mp (hVJ.trans hn)) hv
  change ⁅S,S⁆ ≤ Q
  conv_lhs => lhs; rw [he]
  exact commutator_sup_le_of_relative_normal J Q V S Q hn (pCoreIn_le 2 J) hVJ
    (le_normalizer_iff_commutator_le_left.mp (show S ≤ normalizer (Q : Set G) from le_sup_right.trans hn)) hVS

/-- A nontrivial subgroup of the source overlap normalized by the whole
left parabolic has exactly the right Borel as its normalizer in R. -/
theorem LocalData.zeroCore_right_normalizer_of_left_normal
    {T : Sylow 2 G} {L W H A B D R N : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 = ⊥)
    (hN : N ≤ Global.sourceS L H ⊔ (B ⊓ R)) (hne : N ≠ ⊥)
    (hn : (D ⊔ Global.sourceS L H) ⊔ (B ⊓ R) ≤ normalizer (N : Set G)) :
    R ⊓ normalizer (N : Set G) = (Global.sourceS L H ⊓ R) ⊔ (B ⊓ R) := by
  let S := Global.sourceS L H
  have hf := d.hypothesisF11 h hH c hd hz
  have hSN : S ≤ normalizer (N : Set G) := (le_sup_right.trans le_sup_left).trans hn
  have hproper : R ⊓ normalizer (N : Set G) < R := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro he
    have hRN : R ≤ normalizer (N : Set G) := he ▸ inf_le_right
    apply hne
    exact (d.zeroCore_sylows_and_faithfulness h hH c hd hz).2.2 N hN hn (sup_le hRN hSN)
  have hle := (hf.rankOneBorelFacts 1).unique_maximal (R ⊓ normalizer (N : Set G))
    (le_inf inf_le_right (inf_le_left.trans hSN)) hproper
  change R ⊓ normalizer (N : Set G) ≤ ChapterF.Source.borel R S at hle
  rw [d.right_borel] at hle
  apply le_antisymm hle
  exact le_inf (sup_le inf_le_right inf_le_right)
    ((sup_le (inf_le_left.trans (le_sup_right.trans le_sup_left)) le_sup_right).trans hn)

/-- The derived left core is a large, left-normal subgroup of the opposite
core. Its stabilizer in the selected right factor is exactly its original Borel. -/
theorem LocalData.zeroCore_left_derived_opposite_core
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p f : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 = ⊥)
    (hlin : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^f)) :
    let S := Global.sourceS L H
    let P := (D ⊔ S) ⊔ (B ⊓ R)
    let Q := P.pCoreIn 2
    let N := ⁅Q,Q⁆
    2^n ≤ Nat.card N ∧ N ≠ ⊥ ∧
      N < (R ⊔ S).pCoreIn 2 ∧ 2^(n+1) ≤ Nat.card ((R ⊔ S).pCoreIn 2) ∧
      P ≤ normalizer (N : Set G) ∧
      R ⊓ normalizer (N : Set G) = (S ⊓ R) ⊔ (B ⊓ R) := by
  let S := Global.sourceS L H
  let P := (D ⊔ S) ⊔ (B ⊓ R)
  let Q := P.pCoreIn 2
  let N := ⁅Q,Q⁆
  have hbound := d.left_parabolic_core_derived_bound h hH c hd
  have hne : N ≠ ⊥ := by
    intro he
    change 2^n ≤ Nat.card N at hbound
    rw [he,card_bot] at hbound
    have hp : 2^2 ≤ (2:ℕ)^n := Nat.pow_le_pow_right (by decide) h.exponent
    omega
  obtain ⟨U,hU⟩ := (d.zeroCore_sylows_and_faithfulness h hH c hd hz).1
  have hQS : Q ≤ S := (pCoreIn_le_sylow P U).trans_eq hU
  have hPN : P ≤ normalizer (N : Set G) := by
    have hn : P ≤ normalizer (Q : Set G) :=
      P.le_normalizer.trans (normalizer_le_normalizer_characteristic_image P (pCore 2 P))
    intro x hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [map_commutator,mem_normalizer_iff_map_conj_eq.mp (hn hx)]
  have hNS : N ≤ S := (le_normalizer_iff_commutator_le_left.mp Q.le_normalizer).trans hQS
  let QR := (R ⊔ S).pCoreIn 2
  have hNR : N ≤ QR := (commutator_mono hQS hQS).trans
    (d.zeroCore_sylow_derived_le_right_core h hH c hd hz hlin)
  have hlt : N < QR := by
    refine lt_of_le_of_ne hNR ?_
    intro he
    apply hne
    apply (d.zeroCore_sylows_and_faithfulness h hH c hd hz).2.2 N
      (hNS.trans le_sup_left) hPN
    rw [he]
    exact (R ⊔ S).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (R ⊔ S) (pCore 2 (R ⊔ S : Subgroup G)))
  have hmul : Nat.card N * N.relIndex QR = Nat.card QR := by
    simpa only [relIndex_bot_left] using
      relIndex_mul_relIndex (⊥ : Subgroup G) N QR bot_le hNR
  have hi : 2 ≤ N.relIndex QR := by
    have hp := Nat.card_pos (α := QR)
    have hne1 : N.relIndex QR ≠ 1 := fun he => hlt.not_ge (relIndex_eq_one.mp he)
    have hne0 : N.relIndex QR ≠ 0 := by intro he; rw [he,mul_zero] at hmul; omega
    omega
  have hcard : 2^(n+1) ≤ Nat.card QR := by
    rw [pow_succ]
    change 2^n ≤ Nat.card N at hbound
    nlinarith
  exact ⟨hbound,hne,hlt,hcard,hPN,
    d.zeroCore_right_normalizer_of_left_normal h hH c hd hz
      (hNS.trans le_sup_left) hne hPN⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
