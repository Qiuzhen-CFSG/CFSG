module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CenterPairSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.TorusIntervalSource
/-!
# Torus invariance above the center of R

In the nontrivial-center block, |U|=q³ and |Z(R)|=q². Each nonidentity
member of the odd torus fixes U only inside Z(R). Coprime fixed-point
lifting and orbit counting leave no proper subgroup between Z(R) and U.

Source: Aschbacher–Smith, the invariant-subgroup step of 2.4.20(4), p.535.
-/
public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
theorem source_noncenterless_torus_invariant_interval
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hz : center (d.block.map d.H.subtype) ≠ ⊥)
    (D N : Subgroup G) (hDL : D ≤ d.block.map d.H.subtype)
    (hDodd : Odd (Nat.card D)) (hDcard : Nat.card D = 2^n-1)
    (hDN : D ≤ normalizer (N : Set G))
    (hZN : (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ⊓
      centralizer (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) : Set G)) ≤ N)
    (hNU : N ≤ sourceModule (d.block.map d.H.subtype)) :
    N = (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ⊓
      centralizer (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) : Set G)) ∨
      N=sourceModule (d.block.map d.H.subtype) := by
  let L := d.block.map d.H.subtype
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let U := sourceModule L
  let Z := R ⊓ centralizer (R : Set G)
  have hK := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  let : IsElementaryAbelian 2 U := by
    let := hK.2.1.elementary
    exact IsElementaryAbelian.map L.subtype
  have hbZ := source_distinguished_elementary d hG T hST hsingle hL hM hTM hunique
  have hcZ : Nat.card (center L)=2^n := by
    rw [← card_map_of_injective L.subtype_injective]
    exact (distinguishedZ_of_center_ne_bot d hz) ▸ hbZ.2.1
  have hUcard : Nat.card U=2^n*(2^n*2^n) := by
    rw [show Nat.card U=Nat.card (ChapterC.blockU L) from card_map_of_injective L.subtype_injective]
    have hcF : Nat.card (ChapterC.blockFixed L)=2^n := by
      change Nat.card ((center L).subgroupOf (ChapterC.blockU L))=2^n
      rw [Nat.card_congr (subgroupOfEquivOfLe
        (hK.center_le_module (source_block_core_eq_module d hG T hST hsingle))).toEquiv]
      exact hcZ
    rw [card_eq_card_quotient_mul_card_subgroup (ChapterC.blockFixed L),hK.module_card,hcF]
    rw [show n*2=n+n by omega,pow_add]
    ac_rfl
  have hZcard : Nat.card Z=2^n*2^n := by
    obtain ⟨x,hxT,hxS⟩ := SetLike.exists_of_lt hST
    have hp := source_distinguished_center_pair d hG T hST hsingle hL hM hTM hunique hz x hxT hxS
    let A := distinguishedZ d
    let B := A.map (MulAut.conj x⁻¹).toMonoidHom
    have hAZ : A≤Z := le_sup_left.trans_eq hp.2
    have hBZ : B≤Z := le_sup_right.trans_eq hp.2
    have hn : B≤normalizer (A:Set G) := (hBZ.trans inf_le_right).trans
      ((centralizer_le (hAZ.trans inf_le_left)).trans (Subgroup.centralizer_le_normalizer _))
    have hAB : A⊔B=Z := hp.2
    rw [←hAB,card_sup_eq_mul_of_normalizes_of_disjoint A B hn hp.1,
      card_map_of_injective (MulAut.conj x⁻¹).injective,hbZ.2.1]
  have hDU : D ≤ normalizer (U : Set G) := hDL.trans
    (L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (ChapterC.blockU L)))
  let ρ := U.normalizerMonoidHom.comp (inclusion hDU)
  let : MulDistribMulAction D U := MulDistribMulAction.compHom U ρ
  let N' := N.subgroupOf U
  let : N'.Normal := inferInstance
  have hinv : IsInvariant D U N' := ⟨fun a u => mem_normalizer_iff.mp (hDN a.property) u⟩
  by_cases he : N = U
  · exact Or.inr he
  have hproper : N' ≠ ⊤ := by
    intro ht
    have hm := congrArg (map U.subtype) ht
    rw [map_subgroupOf_eq_of_le hNU,← MonoidHom.range_eq_map,range_subtype] at hm
    exact he hm
  have hcop : Nat.Coprime (Nat.card D) (Nat.card U) := by
    obtain ⟨k,hk⟩ := (IsElementaryAbelian.isPGroup 2 U).exists_card_eq
    rw [hk]
    exact (Nat.coprime_two_right.mpr hDodd).pow_right _
  have hUR : U ≤ R := by
    change sourceModule (d.block.map d.H.subtype) ≤ R
    rw [(lemma_2_4_8_2 d hG T hST hsingle hL hM hTM hunique).2]
    exact le_sSup (d.core_source hG T hST).2.2
  have hf : ∀ a : D, a ≠ 1 → ∀ u : U, a • u = u → u ∈ N' := by
    intro a ha u hu
    have ha1 : (a:G)≠1 := fun he=>ha (Subtype.ext he)
    have haD : zpowers (a:G)≤D := zpowers_le.mpr a.property
    have hcy : zpowers (a:G)≠⊥ := zpowers_ne_bot.mpr ha1
    have hcyodd : Odd (Nat.card (zpowers (a:G))) := hDodd.of_dvd_nat (card_dvd_of_le haD)
    have hfix : (u:G)∈centralizer (zpowers (a:G):Set G) := by
      rw [zpowers_eq_closure,centralizer_closure,mem_centralizer_singleton_iff]
      exact (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hu)).symm
    have hc := source_odd_fixed_centralizes_block d hG T hST hsingle hL (zpowers (a:G))
      (haD.trans hDL) hcyodd hcy ⟨hUR u.property,hfix⟩
    exact hZN ⟨hUR u.property,centralizer_le (show R≤L⊔R from le_sup_right) hc⟩
  have hb := Theory.GroupAction.card_actor_lt_card_quotient_of_fixed_le N' hinv
    (inferInstance : Group.IsSolvable U) hcop hproper hf
  rw [hDcard] at hb
  have hpos : 0 < 2^n := pow_pos (by decide) _
  have hq : 2^n ≤ Nat.card (U ⧸ N') := by omega
  have hcount := card_eq_card_quotient_mul_card_subgroup N'
  rw [hUcard,Nat.card_congr (subgroupOfEquivOfLe hNU).toEquiv] at hcount
  have hNcard : Nat.card N ≤ 2^n * 2^n := by nlinarith
  exact Or.inl (eq_of_le_of_card_ge hZN (hZcard ▸ hNcard)).symm
end CFSG.Quasithin.Chapter2.LinearShadows.Single
