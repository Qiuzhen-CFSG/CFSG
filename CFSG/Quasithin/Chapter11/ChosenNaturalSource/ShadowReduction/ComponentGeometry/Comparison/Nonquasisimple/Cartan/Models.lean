module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveShortlist
public import Theory.SpecificGroups.PSL2.PrimeFieldTwoRank
public import Theory.SpecificGroups.Janko1.Model.InvolutoryTwoComponents
public import Theory.ElementaryAbelian.PrimeRankCard
public import CFSG.Quasithin.Chapter11.Section01To02.SourceDefs

/-!
# Excluding the proper residual overcomponent

The original full-Sylow A₅ seed restricts a quasisimple container to the
proved A₅ shortlist. Order divisibility excludes A₇, its triple cover and
PSL₂(25). A proper prime-field container would make the residual A₅.
For J₁, its elementary Sylow eight cannot act faithfully on PSL₂(p): the
automorphism two-rank is at most two. An involution in the kernel would
put PSL₂(p) in a centralizer of order 120, also impossible for p ≥ 11.

These arguments retain the actual seed and residual inclusions. The
application to N_G(R₁)/O₂(N_G(R₁)) is in Cartan.Complete; it supplies the
embedding exclusion in the nonquasisimple branch of source 11.4.2.
Source: Aschbacher--Smith, printed p.777, using A.3.12--14, pp.47--50.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Cartan
open ChapterA.Section03.SourceEmbeddings
variable {A : Type*} [Group A] [Finite A]

private theorem exceptional_large {p : ℕ} (hp : Source.ExceptionalPrime p) : 11 ≤ p := by
  have h2 := hp.1.two_le
  have h5 := hp.2.1
  have h8 := hp.2.2
  omega

omit [Finite A] in
private theorem prime_dvd_psl_card {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL A 2 p) : p ∣ Nat.card A := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  have hc := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice (hF.symm ▸ ho)
  rw [hF,←Nat.card_congr e.toEquiv] at hc
  have hd : p ∣ 2 * Nat.card A := by
    rw [mul_comm, hc]
    exact dvd_mul_right p _
  exact (hp.dvd_mul.mp hd).resolve_left (fun h =>
    (ho.not_two_dvd_nat) ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h ▸ dvd_rfl))

private theorem exceptional_not_dvd_small {p : ℕ} (hp : Source.ExceptionalPrime p)
    (hd : p ∣ 2 ^ 3 * 3 ^ 3 * 5 ^ 2 * 7 * 13) : False := by
  have hlarge := exceptional_large hp
  have h5 := hp.2.1
  simp only [hp.1.dvd_mul, hp.1.prime.dvd_pow_iff_dvd (by decide : 3 ≠ 0),
    hp.1.prime.dvd_pow_iff_dvd (by decide : 2 ≠ 0),
    Nat.prime_dvd_prime_iff_eq hp.1 (by decide : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hp.1 (by decide : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hp.1 (by decide : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hp.1 (by decide : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hp.1 (by decide : Nat.Prime 13)] at hd
  omega

private theorem janko_centralizer_card (x : Janko1.Model) (hx : orderOf x = 2) :
    Nat.card (centralizer ({x} : Set Janko1.Model)) = 120 := by
  obtain ⟨g,hg⟩ := Janko1.involution_fusion_of_card Janko1.card_model x hx
  let e := MulAut.fixedSubgroupCongr (MulAut.conj g) (MulAut.conj x)
  have he : MulAut.congr (MulAut.conj g) (MulAut.conj x) = MulAut.conj Janko1.a := by
    rw [MulAut.congr_conj]
    exact congrArg MulAut.conj hg
  rw [he] at e
  rw [← MulAut.fixedSubgroup_conj x, Nat.card_congr e.toEquiv,
    MulAut.fixedSubgroup_conj Janko1.a,
    Nat.card_congr Janko1.InvolutionCentralizer.productEquiv.toEquiv]
  change Nat.card (Multiplicative (ZMod 2) × alternatingGroup (Fin 5)) = 120
  rw [Nat.card_prod,nat_card_alternatingGroup]
  norm_num [Nat.factorial]

private theorem not_janko_normalized_psl (S : Sylow 2 Janko1.Model)
    (B : Subgroup Janko1.Model) (hSB : (S : Subgroup Janko1.Model) ≤ normalizer (B : Set Janko1.Model))
    {p : ℕ} (hp : Source.ExceptionalPrime p) (hm : ClassicalGroup.IsPSL B 2 p) : False := by
  have hp3 : 3 < p := by have := exceptional_large hp; omega
  have ho := hp.1.odd_of_ne_two (by omega)
  have hd := prime_dvd_psl_card hp.1 ho hm
  let : IsElementaryAbelian 2 S := Janko1.SylowTwo.elementary S
  have hfaith : (S : Subgroup Janko1.Model) ⊓ centralizer (B : Set Janko1.Model) = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    by_contra hne
    have hxne : x ≠ 1 := by simpa only [mem_bot] using hne
    have hxpow : x ^ 2 = 1 := by
      exact congrArg Subtype.val (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 S) (⟨x,hx.1⟩ : S))
    have hx2 : orderOf x = 2 := orderOf_eq_prime_iff.mpr ⟨hxpow,hxne⟩
    have hBC : B ≤ centralizer ({x} : Set Janko1.Model) := by
      intro b hb
      exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hx.2 b hb)
    have hd120 := hd.trans (card_dvd_of_le hBC)
    rw [janko_centralizer_card x hx2] at hd120
    exact exceptional_not_dvd_small hp (hd120.trans (by decide))
  let f := B.normalizerMonoidHom.comp (inclusion hSB)
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro a ha
    apply Subtype.ext
    apply mem_bot.mp
    rw [←hfaith]
    refine ⟨a.property,?_⟩
    change inclusion hSB a ∈ B.normalizerMonoidHom.ker at ha
    rw [normalizerMonoidHom_ker] at ha
    exact ha
  have hr : 3 ≤ primeRank 2 S := by
    rw [← IsElementaryAbelian.log_card_eq_primeRank (p := 2),Janko1.SylowTwo.card]
    norm_num
  have hrB := hr.trans (_root_.primeRank_le_of_injective 2 f hf)
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fact p.Prime := ⟨hp.1⟩
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod p := FiniteField.ringEquivOfCardEq (by
    rw [←Nat.card_eq_fintype_card,hF,ZMod.card])
  rw [primeRank_equiv 2 (MulAut.congr (e.trans (GorensteinWalter.psl2RingEquiv eF)))] at hrB
  have hu : primeRank 2 (MulAut (GorensteinWalter.PSL2 (ZMod p))) ≤ 2 :=
    Theory.PSL2.primeField_automorphism_two_rank hp3
  omega

/-- The actual normalized A₅ seed forces a prime-field residual to fill
its quasisimple containing component. This uses the proved seed shortlist,
not a universal A.3.12 hypothesis. -/
theorem eq_of_five_seed_and_prime_residual
    (hG : IsSQTK KnownSimple.IsKnownSimple A) (hO : pCore 2 A = ⊥)
    (T : Sylow 2 A) {U B K : Subgroup A}
    (hU : U ∈ ChapterA.Section03.localCComponents T)
    (hTU : (T : Subgroup A) ≤ normalizer (U : Set A))
    (eU : U ≃* alternatingGroup (Fin 5))
    (hB : B ∈ ChapterA.Section03.localCComponents T)
    (hTB : (T : Subgroup A) ≤ normalizer (B : Set A))
    (hK : K.IsCComponent) [IsQuasisimple K]
    (hUB : U ≤ B) (hBK : B ≤ K)
    {p : ℕ} (hp : Source.ExceptionalPrime p)
    (hm : ClassicalGroup.IsPSL B 2 p) : B = K := by
  have hp3 : 3 < p := by have := exceptional_large hp; omega
  have ho := hp.1.odd_of_ne_two (by omega)
  have hd := prime_dvd_psl_card hp.1 ho hm
  have hdK := hd.trans (card_dvd_of_le hBK)
  have hUK := hUB.trans hBK
  obtain ⟨S,hS,hUS,hSU⟩ := exists_local_sylow_normalizing T hU hK.subnormal hUK hTU
  let eUK := (subgroupOfEquivOfLe hUK).trans eU
  have hUn : U.subgroupOf K ≠ ⊤ := by
    intro he
    have he' : U = K := le_antisymm hUK (subgroupOf_eq_top.mp he)
    have hc : Nat.card K = 60 := by
      rw [←he',Nat.card_congr eU.toEquiv,nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    exact exceptional_not_dvd_small hp ((hc ▸ hdK).trans (by decide))
  have hKO : pCore 2 K = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 hK.subnormal,hO,MonoidHom.comap_bot]
    exact K.ker_subtype
  have hs := AlternatingFive.shortlist_knownSimple (hG.subgroup K) hKO S hUS hSU eUK hUn
  rcases hs with ha | hc | hj | h25 | ⟨q,hq,hqmodel⟩
  · have hkcard : Nat.card K = 2520 := by
      rw [Nat.card_congr ha.some.toEquiv,nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    exact (exceptional_not_dvd_small hp ((hkcard ▸ hdK).trans (by decide))).elim
  · have hz : Nat.card (center K) = 3 := by
      rw [Nat.card_congr hc.2.1.some.toEquiv]; simp
    have hq : Nat.card (K ⧸ center K) = 2520 := by
      rw [Nat.card_congr hc.2.2.some.toEquiv,nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    have hkcard : Nat.card K = 7560 := by
      rw [card_eq_card_quotient_mul_card_subgroup (center K),hz,hq]
    exact (exceptional_not_dvd_small hp ((hkcard ▸ hdK).trans (by decide))).elim
  · let e := hj.some
    let B' := (B.subgroupOf K).map e.toMonoidHom
    have hSB : (S : Subgroup K) ≤ normalizer (B.subgroupOf K : Set K) := by
      rw [hS,←subgroupOf_normalizer_eq hBK]
      exact comap_mono hTB
    have hnorm : ((S.mapSurjective (f := e.toMonoidHom) e.surjective) : Subgroup Janko1.Model) ≤
        normalizer (B' : Set Janko1.Model) :=
      (map_mono (f := e.toMonoidHom) hSB).trans (le_normalizer_map e.toMonoidHom)
    have hmodel : ClassicalGroup.IsPSL B' 2 p := hm.of_mulEquiv
      (((B.subgroupOf K).equivMapOfInjective e.toMonoidHom e.injective).symm.trans
        (subgroupOfEquivOfLe hBK))
    exact (not_janko_normalized_psl _ B' hnorm hp hmodel).elim
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := h25
    have hc := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice
      (hF.symm ▸ (by decide : Odd 25))
    rw [hF,←Nat.card_congr e.toEquiv] at hc
    have hkcard : Nat.card K = 7800 := by omega
    exact (exceptional_not_dvd_small hp ((hkcard ▸ hdK).trans (by decide))).elim
  · by_contra hne
    obtain ⟨_,eB⟩ := proper_primePSL2_models T hB hK hBK hne hq.1 hq.2.1 hqmodel
    have hc : Nat.card B = 60 := by
      rw [Nat.card_congr eB.some.toEquiv,nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    exact exceptional_not_dvd_small hp ((hc ▸ hd).trans (by decide))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Cartan
