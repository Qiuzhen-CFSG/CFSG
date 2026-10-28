module
public import CFSG.Quasithin.Chapter4.Section04.OddLocalMathieu.Models
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.AdequateLocal
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.Placement
public import Theory.SpecificGroups.Janko4.Model.Cardinality
public import Theory.SpecificGroups.Janko4.Model.Center
public import Theory.GroupTheory.SimpleSectionSolvableReduction
public import Theory.GroupTheory.CentralizerIndexBound
public import Theory.GroupAction.SubgroupCentralizerCongruence
public import Theory.GroupAction.InnerCentralizerCardinality
public import Theory.Mathieu.M22.Properties.ComponentCentralizer
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.QuotientExtension

/-!
# Excluding the odd-prime J₄ row in the Mathieu comparison

Every automorphism of the actual J₄ carrier is inner. If its fixed group
has an M₂₂ section, an involution in that group restricts the actor prime
to 5, 7 or 11. The section survives quotienting by the central actor, so
the exact J₄ order excludes 5 and 7.

For 11, orbit counting bounds the fixed part of either involution
centralizer's binary kernel by eight. Its quotient maps to Aut(M₂₂),
where an 11-centralizer has two-part at most two. The possible intervening
cubic kernel gives the sufficient bound 48 for each commuting two-group.
A Sylow two-subgroup of the original fixed group must have order at least
128 and fixes an involution there, giving the contradiction.

The argument uses the full literal involution centralizers and their proved
quotient maps. The application is Hall.OddNormalizer.OddLocalSeed.
Source: Aschbacher--Smith 4.4.3, printed p.623, and GLS3 Table 5.3i.
All imported ATLAS matrix certificates retain their source and licenses.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterA.Section02 Sporadic.Mathieu
namespace CFSG.Quasithin.Chapter4.Section04.OddLocalMathieu
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

private theorem mathieu_nonsolvable : ¬ Group.IsSolvable M22 := by
  let : IsSimpleGroup M22 := m22_isSimpleGroup
  have hna : ¬ IsMulCommutative M22 := by
    intro ha
    let := ha
    exact bot_ne_top (m22_center_eq_bot.symm.trans center_eq_top)
  let : Group.IsPerfect M22 := ⟨
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (_root_.commutator M22) inferInstance).resolve_left
      (fun h => hna ((commutator_eq_bot_iff M22).mp h))⟩
  exact Group.IsPerfect.not_isSolvable M22

private theorem mathieu_section_card {X : Type*} [Group X]
    (h : IsSectionOf M22 X) : 443520 ∣ Nat.card X := by
  obtain ⟨B,f,hf⟩ := h
  rw [←m22_order]
  exact (card_dvd_of_surjective f hf).trans B.card_subgroup_dvd_card

/-- A central element contributes its full order in addition to the nonsolvable
Mathieu section, which survives quotienting by the center. -/
theorem mathieu_section_central_order_dvd {X : Type*} [Group X] [Finite X]
    (h : IsSectionOf M22 X) (x : X) (hx : x ∈ center X) :
    orderOf x * 443520 ∣ Nat.card X := by
  let : IsSimpleGroup M22 := m22_isSimpleGroup
  let : Group.IsSolvable (center X) := Group.isSolvable_of_comm
    (fun a b => Subtype.ext (mem_center_iff.mp a.property b).symm)
  obtain ⟨U,f,hf⟩ := h
  have hq : IsSectionOf M22 (X ⧸ center X) :=
    simple_section_quotient_of_solvable_kernel mathieu_nonsolvable (center X) U f hf
  have hd := mathieu_section_card hq
  have hc : orderOf x ∣ Nat.card (center X) := by
    rw [orderOf_coe (⟨x,hx⟩ : center X)]
    exact orderOf_dvd_natCard (⟨x,hx⟩ : center X)
  rw [(center X).card_eq_card_quotient_mul_card_subgroup, Nat.mul_comm (orderOf x)]
  exact Nat.mul_dvd_mul hd hc

private theorem involution_centralizer_prime {p : ℕ} (hp : p.Prime)
    (z : Janko4.Model) (hz : orderOf z = 2)
    (hd : p ∣ Nat.card (centralizer ({z} : Set Janko4.Model))) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 := by
  have hn : p ∣ 21799895040 := by
    rcases Janko4.InvolutionCentralizers.centralizer_equiv_first_or_second z hz with h1 | h2
    · obtain ⟨e⟩ := h1
      rwa [Nat.card_congr e.toEquiv,Janko4.OuterReduction.OddIndex.modelCentralizer_card] at hd
    · obtain ⟨e⟩ := h2
      rw [Nat.card_congr e.toEquiv,Janko4.InvolutionCentralizers.Second.ambient_card] at hd
      exact hd.trans (by decide)
  rw [show 21799895040 = 2^21 * 3^3 * 5 * 7 * 11 by norm_num] at hn
  simpa only [hp.dvd_mul,hp.prime.dvd_pow_iff_dvd (by decide : 21 ≠ 0),
    hp.prime.dvd_pow_iff_dvd (by decide : 3 ≠ 0),Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 11),or_assoc] using hn

/-- Among primes greater than three, only eleven can centralize a Mathieu
section in the actual J₄ carrier. The remaining eleven case is separate. -/
theorem janko_mathieu_centralizer_prime {p : ℕ} (hp : p.Prime) (hpgt : 3 < p)
    (t : Janko4.Model) (ht : orderOf t = p)
    (h : IsSectionOf M22 (centralizer ({t} : Set Janko4.Model))) : p = 11 := by
  let C := centralizer ({t} : Set Janko4.Model)
  have heven : 2 ∣ Nat.card C := (by decide : 2 ∣ 443520).trans (mathieu_section_card h)
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 heven
  have htz : t ∈ centralizer ({(z : Janko4.Model)} : Set Janko4.Model) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp z.property).symm
  have hd : p ∣ Nat.card (centralizer ({(z : Janko4.Model)} : Set Janko4.Model)) := by
    rw [←ht,orderOf_coe (⟨t,htz⟩ : centralizer ({(z : Janko4.Model)} : Set Janko4.Model))]
    exact orderOf_dvd_natCard _
  have hs := involution_centralizer_prime hp z ((orderOf_coe z).trans hz) hd
  have htC : t ∈ C := mem_centralizer_singleton_iff.mpr rfl
  have htc : (⟨t,htC⟩ : C) ∈ center C := by
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp y.property
  have hcard := (mathieu_section_central_order_dvd h (⟨t,htC⟩ : C) htc).trans
    C.card_subgroup_dvd_card
  rw [←orderOf_coe (⟨t,htC⟩ : C),ht,Janko4.Cardinality.model_card] at hcard
  rcases hs with h2 | h3 | h5 | h7 | h11
  · omega
  · omega
  · rw [h5] at hcard; norm_num at hcard
  · rw [h7] at hcard; norm_num at hcard
  · exact h11


private theorem m22_eleven_centralizer_odd (t : M22) (ht : orderOf t = 11) :
    ¬ 2 ∣ Nat.card (centralizer ({t} : Set M22)) := by
  intro he
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := centralizer ({t} : Set M22)) 2 he
  have htz : t ∈ centralizer ({(z : M22)} : Set M22) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp z.property).symm
  have hd := orderOf_dvd_natCard (⟨t,htz⟩ : centralizer ({(z : M22)} : Set M22))
  rw [←orderOf_coe (⟨t,htz⟩ : centralizer ({(z : M22)} : Set M22)),ht,
    M22FourNormalizers.involution_centralizer_card z ((orderOf_coe z).trans hz)] at hd
  norm_num at hd

private theorem m22_eleven_twoGroup_card (a : MulAut M22) (ha : orderOf a = 11)
    (U : Subgroup (MulAut M22)) (hU : IsPGroup 2 U)
    (hC : U ≤ centralizer ({a} : Set (MulAut M22))) : Nat.card U ≤ 2 := by
  let q := QuotientGroup.mk' (MulAut.innerSubgroup M22)
  have houter : Nat.card (MulAut.Outer M22) ∣ 2 := m22_inner_index_dvd_two
  have hqa : q a = 1 := by
    apply orderOf_eq_one_iff.mp
    apply Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 11 2)
    · simpa only [ha] using orderOf_map_dvd q a
    · exact (_root_.orderOf_dvd_natCard (q a)).trans houter
  have haI : a ∈ MulAut.innerSubgroup M22 := by
    exact (QuotientGroup.eq_one_iff _).mp hqa
  obtain ⟨t,ht⟩ := haI
  have ht11 : orderOf t = 11 := by
    rw [←MulAut.conj_orderOf_of_center_eq_bot m22_center_eq_bot t,ht]
    exact ha
  rw [←ht] at hC
  have hd := (card_dvd_of_le hC).trans (MulAut.centralizer_conj_card_dvd m22_center_eq_bot t |>.trans
    (Nat.mul_dvd_mul_left _ houter))
  obtain ⟨n,hn⟩ := hU.exists_card_eq
  rw [hn] at hd ⊢
  have hc : Nat.Coprime (2^n) (Nat.card (centralizer ({t} : Set M22))) :=
    (Nat.prime_two.coprime_iff_not_dvd.mpr (m22_eleven_centralizer_odd t ht11)).pow_left _
  exact Nat.le_of_dvd (by decide : 0 < 2) (hc.dvd_of_dvd_mul_left hd)

/-- An element of order eleven fixes at most eight elements in either size
of self-centralizing binary kernel occurring in a J₄ involution centralizer. -/
theorem eleven_core_fixed_card_le_eight {X : Type*} [Group X] [Finite X]
    (Q : Subgroup X) [Q.Normal] (hQ : IsPGroup 2 Q)
    (hcard : Nat.card Q = 2048 ∨ Nat.card Q = 8192)
    (hself : centralizer (Q : Set X) ≤ Q)
    (t : X) (ht : orderOf t = 11) :
    Nat.card (Q ⊓ centralizer ({t} : Set X) : Subgroup X) ≤ 8 := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  let F := Q ⊓ centralizer ({t} : Set X)
  have hF : IsPGroup 2 F := hQ.of_injective (inclusion inf_le_left) (inclusion_injective inf_le_left)
  have hA : IsPGroup 11 (zpowers t) := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers,ht,pow_one])
  have hm := card_modEq_card_inf_centralizer (zpowers t) Q hA
    (le_normalizer_of_normal (H := Q))
  rw [zpowers_eq_closure,centralizer_closure] at hm
  change Nat.card Q % 11 = Nat.card F % 11 at hm
  have hlt : Nat.card F < Nat.card Q := by
    apply lt_of_le_of_ne (card_le_of_le inf_le_left)
    intro he
    have heq : F = Q := eq_of_le_of_card_ge inf_le_left he.ge
    have htc : t ∈ centralizer (Q : Set X) := by
      intro y hy
      have hh := (show Q ≤ centralizer ({t} : Set X) from heq ▸ inf_le_right) hy
      exact mem_centralizer_singleton_iff.mp hh
    have hd := orderOf_dvd_natCard (⟨t,hself htc⟩ : Q)
    rw [←orderOf_coe (⟨t,hself htc⟩ : Q),ht] at hd
    rcases hcard with hc | hc <;> rw [hc] at hd <;> norm_num at hd
  obtain ⟨k,hk⟩ := hF.exists_card_eq
  have hb : k < 13 := by
    have hb : 2^k < 2^13 := by rcases hcard with hc | hc <;> rw [hc,hk] at hlt <;> omega
    exact (Nat.pow_lt_pow_iff_right (by decide)).mp hb
  rw [hk]
  rcases hcard with hc | hc <;> rw [hc,hk] at hm hlt <;>
    interval_cases k <;> norm_num at *



/-- The genuine binary kernel and its at-most-cubic enlargement bound any
two-subgroup centralizing an element of order eleven. -/
theorem eleven_twoGroup_card_le_fortyEight {X : Type*} [Group X] [Finite X]
    (Q : Subgroup X) [Q.Normal] (hQ : IsPGroup 2 Q)
    (hcard : Nat.card Q = 2048 ∨ Nat.card Q = 8192)
    (hself : centralizer (Q : Set X) ≤ Q)
    (f : X →* MulAut M22) (hQf : Q ≤ f.ker) (hi : Q.relIndex f.ker ≤ 3)
    (hker : ¬ 11 ∣ Nat.card f.ker)
    (t : X) (ht : orderOf t = 11) (U : Subgroup X) (hU : IsPGroup 2 U)
    (hUC : U ≤ centralizer ({t} : Set X)) : Nat.card U ≤ 48 := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  have ht' : orderOf (f t) = 11 := by
    apply orderOf_eq_prime
    · have he : t^11 = 1 := ht ▸ pow_orderOf_eq_one t
      rw [←map_pow,he,map_one]
    · intro hh
      have hd := _root_.orderOf_dvd_natCard (⟨t,hh⟩ : f.ker)
      rw [←orderOf_coe (⟨t,hh⟩ : f.ker),ht] at hd
      exact hker hd
  have himage : Nat.card (U.map f) ≤ 2 := by
    apply m22_eleven_twoGroup_card (f t) ht' (U.map f) (hU.map f)
    rintro _ ⟨u,hu,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    simpa only [map_mul] using congrArg f (mem_centralizer_singleton_iff.mp (hUC hu))
  have hindex : Q.relIndex U ≤ 6 := by
    have hmul := relIndex_inf_mul_relIndex Q f.ker U
    rw [inf_of_le_left hQf,relIndex_ker] at hmul
    have hb : Q.relIndex (f.ker ⊓ U) ≤ 3 :=
      (relIndex_le_of_le_right inf_le_left (show Q.relIndex f.ker ≠ 0 from index_ne_zero_of_finite)).trans hi
    rw [←hmul]
    exact (Nat.mul_le_mul hb himage).trans_eq (by decide)
  have hf : Nat.card ((centralizer ({t} : Set X)).subgroupOf Q) ≤ 8 := by
    rw [←inf_subgroupOf_right]
    rw [Nat.card_congr (subgroupOfEquivOfLe (show
      (centralizer ({t} : Set X) ⊓ Q : Subgroup X) ≤ Q from inf_le_right)).toEquiv,inf_comm]
    exact eleven_core_fixed_card_le_eight Q hQ hcard hself t ht
  exact (card_le_centralizer_card_mul_relIndex U Q {t} hUC).trans
    ((Nat.mul_le_mul hf hindex).trans_eq (by decide))



private theorem first_eleven_twoGroup_card
    (t : Janko4.InvolutionCentralizers.First.centralizer) (ht : orderOf t = 11)
    (U : Subgroup Janko4.InvolutionCentralizers.First.centralizer) (hU : IsPGroup 2 U)
    (hUC : U ≤ centralizer ({t} : Set Janko4.InvolutionCentralizers.First.centralizer)) :
    Nat.card U ≤ 48 := by
  let Q := Janko4.InvolutionCentralizers.First.QuotientExtension.Q
  let f := Janko4.InvolutionCentralizers.First.QuotientExtension.centralizerMathieuAction
  have hqf : Q ≤ f.ker := by
    rw [Janko4.InvolutionCentralizers.First.QuotientExtension.centralizerMathieuAction_ker]
    exact Janko4.InvolutionCentralizers.First.QuotientExtension.Q_le_R
  have hi : Q.relIndex f.ker = 3 := by
    rw [Janko4.InvolutionCentralizers.First.QuotientExtension.centralizerMathieuAction_ker]
    change (Q.subgroupOf Janko4.InvolutionCentralizers.First.QuotientExtension.R).index = 3
    rw [index_eq_card,Nat.card_congr
      Janko4.InvolutionCentralizers.First.QuotientExtension.RQuotientEquivC3.toEquiv]
    simp only [Nat.card_eq_fintype_card,Fintype.card_multiplicative,ZMod.card]
  have hc : Nat.card Q = 8192 :=
    Janko4.InvolutionCentralizers.First.centralizer_twoCore_card
  have hk : Nat.card f.ker = 24576 := by
    have hm := relIndex_mul_relIndex (⊥ : Subgroup _) Q f.ker bot_le hqf
    rw [relIndex_bot_left,relIndex_bot_left,hi,hc] at hm
    exact hm.symm
  exact eleven_twoGroup_card_le_fortyEight Q pCore_isPGroup (Or.inr hc)
    Janko4.InvolutionCentralizers.first_characteristic_two f hqf hi.le
    (by rw [hk]; decide) t ht U hU hUC

private theorem second_eleven_twoGroup_card
    (t : Janko4.InvolutionCentralizers.Second.ambientCentralizer) (ht : orderOf t = 11)
    (U : Subgroup Janko4.InvolutionCentralizers.Second.ambientCentralizer) (hU : IsPGroup 2 U)
    (hUC : U ≤ centralizer ({t} : Set Janko4.InvolutionCentralizers.Second.ambientCentralizer)) :
    Nat.card U ≤ 48 := by
  let Q := Janko4.InvolutionCentralizers.Second.ambientKernel
  let f := Janko4.InvolutionCentralizers.Second.ambientExtension.rightHom
  let := Janko4.InvolutionCentralizers.Second.ambientKernel_elementary
  exact eleven_twoGroup_card_le_fortyEight Q (IsElementaryAbelian.isPGroup 2 _)
    (Or.inl Janko4.InvolutionCentralizers.Second.ambientKernel_card)
    Janko4.InvolutionCentralizers.Second.ambientKernel_selfCentralizing.le f le_rfl
    (by change Q.relIndex Q ≤ 3; rw [relIndex_self]; decide)
    (by change ¬11 ∣ Nat.card Q; rw [Janko4.InvolutionCentralizers.Second.ambientKernel_card]; decide)
    t ht U hU hUC

/-- In either actual involution centralizer of J₄, a two-group commuting with
an element of order eleven has order at most 48. -/
theorem janko_involution_eleven_twoGroup_card (z : Janko4.Model) (hz : orderOf z = 2)
    (t : centralizer ({z} : Set Janko4.Model)) (ht : orderOf t = 11)
    (U : Subgroup (centralizer ({z} : Set Janko4.Model))) (hU : IsPGroup 2 U)
    (hUC : U ≤ centralizer ({t} : Set (centralizer ({z} : Set Janko4.Model)))) : Nat.card U ≤ 48 := by
  have step {Y : Type} [Group Y]
      (e : centralizer ({z} : Set Janko4.Model) ≃* Y)
      (hbound : ∀ (v : Y), orderOf v = 11 → ∀ (W : Subgroup Y), IsPGroup 2 W →
        W ≤ centralizer ({v} : Set Y) → Nat.card W ≤ 48) : Nat.card U ≤ 48 := by
    have hN : U.map e.toMonoidHom ≤ centralizer ({e t} : Set Y) := by
      rw [←Set.image_singleton,←map_centralizer_equiv]
      exact map_mono hUC
    have hb := hbound (e t) ((e.orderOf_eq t).trans ht) (U.map e.toMonoidHom) (hU.map _) hN
    rwa [card_map_of_injective e.injective] at hb
  rcases Janko4.InvolutionCentralizers.centralizer_equiv_first_or_second z hz with h | h
  · obtain ⟨e⟩ := h
    exact step e first_eleven_twoGroup_card
  · obtain ⟨e⟩ := h
    exact step e second_eleven_twoGroup_card



/-- No element of order eleven in J₄ can centralize a Mathieu section: the
original centralizer's Sylow two-subgroup would have order at least 128. -/
theorem no_janko_eleven_mathieu_centralizer (t : Janko4.Model) (ht : orderOf t = 11) :
    ¬ IsSectionOf M22 (centralizer ({t} : Set Janko4.Model)) := by
  intro h
  let C := centralizer ({t} : Set Janko4.Model)
  let P : Sylow 2 C := Sylow.nonempty.some
  let U := (P : Subgroup C).map C.subtype
  have hU : IsPGroup 2 U := P.isPGroup'.map _
  have hUC : U ≤ C := map_subtype_le _
  have hAn : U ≤ normalizer (zpowers t : Set Janko4.Model) := by
    have heq : centralizer (zpowers t : Set Janko4.Model) = C := by
      rw [zpowers_eq_closure,centralizer_closure]
    exact (hUC.trans_eq heq.symm).trans (centralizer_le_normalizer _)
  have he : 2 ∣ Nat.card (centralizer (zpowers t : Set Janko4.Model)) := by
    rw [zpowers_eq_closure,centralizer_closure]
    exact (by decide : 2 ∣ 443520).trans (mathieu_section_card h)
  obtain ⟨z,hz,hzle⟩ := exists_involution_centralizing_normalizing_two_group (zpowers t) U hU hAn he
  have htZ : t ∈ centralizer ({z} : Set Janko4.Model) := (le_sup_left.trans hzle) (mem_zpowers t)
  have hUZ : U ≤ centralizer ({z} : Set Janko4.Model) := le_sup_right.trans hzle
  let Z := centralizer ({z} : Set Janko4.Model)
  let v : Z := ⟨t,htZ⟩
  have hW : IsPGroup 2 (U.subgroupOf Z) := hU.of_injective (subgroupOfEquivOfLe hUZ).toMonoidHom (subgroupOfEquivOfLe hUZ).injective
  have hWC : U.subgroupOf Z ≤ centralizer ({v} : Set Z) := by
    intro u hu
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (hUC hu)
  have hb := janko_involution_eleven_twoGroup_card z hz v
    ((orderOf_coe v).symm.trans ht) (U.subgroupOf Z) hW hWC
  rw [Nat.card_congr (subgroupOfEquivOfLe hUZ).toEquiv,card_map_of_injective C.subtype_injective] at hb
  have hd : 2^7 ∣ Nat.card P := P.pow_dvd_card_of_pow_dvd_card
    ((by decide : 2^7 ∣ 443520).trans (mathieu_section_card h))
  have hl := Nat.le_of_dvd (Nat.card_pos (α := P)) hd
  omega

/-- The J₄ row of the p.623 odd-local comparison is impossible for p > 3.
The actor and Mathieu section are literal subgroups of the native carrier. -/
theorem no_janko_mathieu_fixed_section {p : ℕ} (hp : p.Prime) (hpgt : 3 < p) :
    ¬ HasMathieuFixedSection Janko4.Model p := by
  rintro ⟨a,ha,h⟩
  obtain ⟨t,rfl⟩ := Janko4.AdequateLocal.exists_eq_conj a
  have ht : orderOf t = p :=
    (MulAut.conj_orderOf_of_center_eq_bot Janko4.model_center_eq_bot t).symm.trans ha
  rw [MulAut.fixedSubgroup_conj] at h
  have hp11 := janko_mathieu_centralizer_prime hp hpgt t ht h
  exact no_janko_eleven_mathieu_centralizer t (ht.trans hp11) h

end CFSG.Quasithin.Chapter4.Section04.OddLocalMathieu
