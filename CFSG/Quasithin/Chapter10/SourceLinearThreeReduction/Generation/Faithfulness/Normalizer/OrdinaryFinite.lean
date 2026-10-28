module
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.SourceA5Normality
public import Theory.GroupTheory.PerfectPairOrder

/-!
# Ordinary covering rows for a centerless seed

The actual C.2.8 span embeds in each ordinary component, with odd ranks
preserved by its central quotient. Burnside supplies an odd prime outside
any chosen prime; rank at most one there makes the original seed normal.
Certified orders and the binary rank-two parabolics exclude the finite,
linear, symplectic, G₂ and triality rows. The Tits row also uses the literal
nontrivial radical normalizer and its fifteen-free order.

OrdinaryModels and OrdinarySource apply these results to the original
covering and Hall-kernel configurations; no A₅ marking is imposed.
Source: Aschbacher--Smith C.3.5 and C.4.8, pp.150--154, used by
4.2.12 and 4.4.6, pp.610,620, in 10.2.3(2), p.745.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G : Type*} [Group G] [Finite G] {H M L R V : Subgroup G}

theorem normalizes_of_simple_span_prime_divisor
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    [IsQuasisimple (L ⧸ pCore 2 L)] (hz : center (L ⧸ pCore 2 L) = ⊥)
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hd : p ∣ Nat.card (L ⧸ pCore 2 L))
    (hr : primeRank p (conjugateSpanBy L M) ≤ 1) : M ≤ normalizer (L : Set G) := by
  have hp : 0 < primeRank p (L ⧸ pCore 2 L) := by
    have hh : primeRank p (L ⧸ pCore 2 L) ≠ 0 :=
      fun he => PrimeRank.eq_zero_iff_not_dvd_card.mp he hd
    omega
  exact h.normalizes_of_span_odd_rank ho hz hp (by omega)

theorem normalizes_of_simple_span_odd_ranks
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    [IsQuasisimple (L ⧸ pCore 2 L)] (hz : center (L ⧸ pCore 2 L) = ⊥)
    {q : ℕ} (hq : q.Prime)
    (hr : ∀ p : ℕ, p.Prime → Odd p → p ≠ q → primeRank p (conjugateSpanBy L M) ≤ 1) :
    M ≤ normalizer (L : Set G) := by
  let : IsSimpleGroup ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) := IsQuasisimple.simple
  let : Nontrivial (L ⧸ pCore 2 L) :=
    (QuotientGroup.mk'_surjective (center (L ⧸ pCore 2 L))).nontrivial
  obtain ⟨p,hp,ho,hne,hd⟩ := Perfect.exists_odd_prime_ne_dvd_card (L ⧸ pCore 2 L) hq
  let : Fact p.Prime := ⟨hp⟩
  exact h.normalizes_of_simple_span_prime_divisor hz ho hd (hr p hp ho hne)

theorem normalizes_of_simple_ordinary_quotient_ranks
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    [IsQuasisimple (L ⧸ pCore 2 L)] (hz : center (L ⧸ pCore 2 L) = ⊥)
    (K : Subgroup H) (hK : IsComponent H K) {q : ℕ} (hq : q.Prime)
    (hr : ∀ p : ℕ, p.Prime → Odd p → p ≠ q → primeRank p (K ⧸ center K) ≤ 1) :
    M ≤ normalizer (L : Set G) := by
  apply h.normalizes_of_simple_span_odd_ranks hz hq
  intro p hp ho hne
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨_,_,_,_,he⟩ := h.ordinary_quotient_local_data K hK
  rw [←he p hp ho]
  exact (primeRank_subgroup_le p _).trans (hr p hp ho hne)

theorem normalizes_of_simple_ordinary_quotient_order
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    [IsQuasisimple (L ⧸ pCore 2 L)] (hz : center (L ⧸ pCore 2 L) = ⊥)
    (K : Subgroup H) (hK : IsComponent H K)
    {q a b c : ℕ} (hq : q.Prime) (hc : Squarefree c)
    (hd : Nat.card (K ⧸ center K) ∣ 2 ^ a * q ^ b * c) :
    M ≤ normalizer (L : Set G) := by
  apply h.normalizes_of_simple_ordinary_quotient_ranks hz K hK hq
  intro p hp ho hne
  let : Fact p.Prime := ⟨hp⟩
  exact primeRank_le_one_of_card_dvd_two_prime_squarefree _ hq ho hne hc hd

private theorem squarefree_35 : Squarefree (35 : ℕ) :=
  (Nat.squarefree_mul (show Nat.Coprime 5 7 by decide)).mpr
    ⟨(Nat.prime_iff.mp (by decide : Nat.Prime 5)).squarefree,
      (Nat.prime_iff.mp (by decide : Nat.Prime 7)).squarefree⟩
private theorem squarefree_55 : Squarefree (55 : ℕ) :=
  (Nat.squarefree_mul (show Nat.Coprime 5 11 by decide)).mpr
    ⟨(Nat.prime_iff.mp (by decide : Nat.Prime 5)).squarefree,
      (Nat.prime_iff.mp (by decide : Nat.Prime 11)).squarefree⟩
private theorem squarefree_385 : Squarefree (385 : ℕ) :=
  (Nat.squarefree_mul (show Nat.Coprime 35 11 by decide)).mpr
    ⟨squarefree_35, (Nat.prime_iff.mp (by decide : Nat.Prime 11)).squarefree⟩
private theorem squarefree_1085 : Squarefree (1085 : ℕ) :=
  (Nat.squarefree_mul (show Nat.Coprime 35 31 by decide)).mpr
    ⟨squarefree_35, (Nat.prime_iff.mp (by decide : Nat.Prime 31)).squarefree⟩
private theorem squarefree_8855 : Squarefree (8855 : ℕ) :=
  (Nat.squarefree_mul (show Nat.Coprime 385 23 by decide)).mpr
    ⟨squarefree_385, (Nat.prime_iff.mp (by decide : Nat.Prime 23)).squarefree⟩

variable (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    [IsQuasisimple (L ⧸ pCore 2 L)] (hz : center (L ⧸ pCore 2 L) = ⊥)
    (K : Subgroup H) (hK : IsComponent H K)
include h hz hK

theorem normalizes_of_simple_ordinary_alternating
    {n : ℕ} (hn : n ≤ 9) (e : K ⧸ center K ≃* alternatingGroup (Fin n)) :
    M ≤ normalizer (L : Set G) := by
  apply h.normalizes_of_simple_ordinary_quotient_ranks hz K hK Nat.prime_three
  intro p hp ho hne
  let : Fact p.Prime := ⟨hp⟩
  rw [primeRank_congr p e,
    GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime n p hp
      (by intro he; subst p; exact ho.not_two_dvd_nat (dvd_refl 2))]
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    have hodd := ho.not_two_dvd_nat
    omega
  exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hp.pos).mpr (by omega))

theorem normalizes_of_simple_ordinary_binary_linear
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (hm : ClassicalGroup.IsPSL (K ⧸ center K) n 2) : M ≤ normalizer (L : Set G) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  rcases hn with rfl | rfl
  · have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 4
    norm_num [hF,Fin.prod_univ_succ] at hc
    apply h.normalizes_of_simple_ordinary_quotient_order hz K hK
      (q := 3) (a := 6) (b := 2) (c := 35) Nat.prime_three squarefree_35
    rw [Nat.card_congr e.toEquiv,hc]
    decide
  · have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 5
    norm_num [hF,Fin.prod_univ_succ] at hc
    apply h.normalizes_of_simple_ordinary_quotient_order hz K hK
      (q := 3) (a := 10) (b := 2) (c := 1085) Nat.prime_three squarefree_1085
    rw [Nat.card_congr e.toEquiv,hc]
    decide

theorem normalizes_of_simple_ordinary_g2_derived_two
    (e : K ⧸ center K ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    M ≤ normalizer (L : Set G) := by
  apply h.normalizes_of_simple_ordinary_quotient_order hz K hK
    (q := 3) (a := 5) (b := 3) (c := 7) Nat.prime_three
      (Nat.prime_iff.mp (by decide : Nat.Prime 7)).squarefree
  rw [Nat.card_congr e.toEquiv,Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)]
  decide

theorem normalizes_of_simple_ordinary_mathieu
    (n : ClassificationModels.SporadicName)
    (hn : n = .m11 ∨ n = .m12 ∨ n = .m22 ∨ n = .m23 ∨ n = .m24)
    (e : K ⧸ center K ≃* n.Carrier) : M ≤ normalizer (L : Set G) := by
  rcases hn with rfl | rfl | rfl | rfl | rfl
  · apply h.normalizes_of_simple_ordinary_quotient_order hz K hK
      (q := 3) (a := 4) (b := 2) (c := 55) Nat.prime_three squarefree_55
    rw [Nat.card_congr e.toEquiv]
    change Nat.card Sporadic.Mathieu.M11 ∣ _
    rw [Sporadic.Mathieu.m11_order]; decide
  · apply h.normalizes_of_simple_ordinary_quotient_order hz K hK
      (q := 3) (a := 6) (b := 3) (c := 55) Nat.prime_three squarefree_55
    rw [Nat.card_congr e.toEquiv]
    change Nat.card Sporadic.Mathieu.M12 ∣ _
    rw [Sporadic.Mathieu.m12_order]; decide
  · apply h.normalizes_of_simple_ordinary_quotient_order hz K hK
      (q := 3) (a := 7) (b := 2) (c := 385) Nat.prime_three squarefree_385
    rw [Nat.card_congr e.toEquiv]
    change Nat.card Sporadic.Mathieu.M22 ∣ _
    rw [Sporadic.Mathieu.m22_order]; decide
  · apply h.normalizes_of_simple_ordinary_quotient_order hz K hK
      (q := 3) (a := 7) (b := 2) (c := 8855) Nat.prime_three squarefree_8855
    rw [Nat.card_congr e.toEquiv]
    change Nat.card Sporadic.Mathieu.M23 ∣ _
    rw [Sporadic.Mathieu.m23_order]; decide
  · apply h.normalizes_of_simple_ordinary_quotient_order hz K hK
      (q := 3) (a := 10) (b := 3) (c := 8855) Nat.prime_three squarefree_8855
    rw [Nat.card_congr e.toEquiv]
    change Nat.card Sporadic.Mathieu.M24 ∣ _
    rw [Sporadic.Mathieu.m24_order]; decide

theorem normalizes_of_simple_ordinary_symplectic
    {n : ℕ} (hm : ClassicalGroup.IsPSp (K ⧸ center K) 2 (2 ^ n)) :
    M ≤ normalizer (L : Set G) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  apply h.normalizes_of_simple_span_odd_ranks hz Nat.prime_three
  intro p hp ho _
  let : Fact p.Prime := ⟨hp⟩
  exact h.ordinary_span_primeRank_le_one_of_sp4 K hK
    (e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm) ho

theorem normalizes_of_simple_ordinary_g2
    {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassificationModels.IsG2At (K ⧸ center K) (2 ^ n)) :
    M ≤ normalizer (L : Set G) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  apply h.normalizes_of_simple_span_odd_ranks hz Nat.prime_three
  intro p hp ho _
  let : Fact p.Prime := ⟨hp⟩
  exact h.ordinary_span_primeRank_le_one_of_g2 K hK e
    (by
      rw [hF]
      exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
        (Nat.pow_le_pow_right (by decide) hn)) ho

theorem normalizes_of_simple_ordinary_triality
    {n : ℕ} (hn : 1 ≤ n)
    (hm : Triality.Standard.IsTrialityGroupAt (2 ^ n) (K ⧸ center K)) :
    M ≤ normalizer (L : Set G) := by
  apply h.normalizes_of_simple_span_odd_ranks hz Nat.prime_three
  intro p hp ho _
  let : Fact p.Prime := ⟨hp⟩
  exact h.ordinary_span_primeRank_le_one_of_isTrialityGroupAt K hK hn hm ho

theorem normalizes_of_simple_ordinary_linear_three
    {n : ℕ} (hn : 1 ≤ n)
    (hm : ClassicalGroup.IsPSL (K ⧸ center K) 3 (2 ^ n)) :
    M ≤ normalizer (L : Set G) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  by_cases hn1 : n = 1
  · apply h.normalizes_of_simple_ordinary_quotient_order hz K hK
      (q := 3) (a := 3) (b := 1) (c := 7) Nat.prime_three
      (Nat.prime_iff.mp (by decide : Nat.Prime 7)).squarefree
    rw [Nat.card_congr e.toEquiv]
    have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
    norm_num [hF,hn1,Fin.prod_univ_succ] at hc
    rw [hc]; decide
  apply h.normalizes_of_simple_span_odd_ranks hz Nat.prime_three
  intro p hp ho _
  let : Fact p.Prime := ⟨hp⟩
  apply h.ordinary_span_primeRank_le_of_model_two_normalizers K hK e ho
  intro X P hX hP hne hnP
  let := hX
  by_contra! hb
  obtain ⟨g,point,hg⟩ :=
    MainConverse.LinearThreeGeometry.twoLocal_conjugate_le F hn hF
      (normalizer (P : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F))) ⟨P,hne,hP,rfl⟩
  let j := (MulAut.conj g).toMonoidHom.comp X.subtype
  have hj : j.range ≤ Matrix.PSL3.RootPlaneGeometry.parabolic F point := by
    refine le_trans ?_ hg
    rintro _ ⟨a,rfl⟩
    exact mem_map_of_mem _ (hnP a.property)
  apply Matrix.PSL3.LinearThree.PerfectSubgroups.no_perfect_odd_rank_two_in_parabolic
    F ho (by omega) (by
      rw [hF]
      exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2 ≤ n))
    j ((MulAut.conj g).injective.comp X.subtype_injective)
  cases point
  · exact Or.inr hj
  · exact Or.inl hj

theorem normalizes_of_simple_ordinary_tits
    (e : K ⧸ center K ≃* Tits.ParrottGroup) : M ≤ normalizer (L : Set G) := by
  obtain ⟨_,hP,hne,hn,hr⟩ := h.ordinary_quotient_local_data K hK
  let A := (((conjugateSpanBy L M).subgroupOf H).subgroupOf K).map
    (QuotientGroup.mk' (center K))
  let P := ((R.subgroupOf H).subgroupOf K).map (QuotientGroup.mk' (center K))
  let N := normalizer (P.map e.toMonoidHom : Set Tits.ParrottGroup)
  have hAN : A.map e.toMonoidHom ≤ N :=
    (map_mono hn).trans (P.le_normalizer_map e.toMonoidHom)
  have h15 : ¬ 15 ∣ Nat.card N := Tits.normalizer_fifteen_free _
    (fun he => hne ((map_eq_bot_iff_of_injective P e.injective).mp he)) (hP.map _)
  have hd : Nat.card N ∣ 17971200 := by
    simpa only [Tits.parrottGroup_card] using N.card_subgroup_dvd_card
  have hbound : ∃ q : ℕ, q.Prime ∧
      ∀ p : ℕ, p.Prime → Odd p → p ≠ q → primeRank p N ≤ 1 := by
    by_cases h3 : 3 ∣ Nat.card N
    · have h5 : ¬ 5 ∣ Nat.card N := fun he =>
        h15 ((show Nat.Coprime 3 5 by decide).mul_dvd_of_dvd_of_dvd h3 he)
      have hc : Nat.Coprime (Nat.card N) (5 ^ 2) :=
        ((Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 5)).mpr h5).symm.pow_right 2
      have hd' : Nat.card N ∣ 2 ^ 11 * 3 ^ 3 * 13 := hc.dvd_mul_left.mp
        (by convert hd using 1; norm_num)
      refine ⟨3,Nat.prime_three,?_⟩
      intro p hp ho hne
      let : Fact p.Prime := ⟨hp⟩
      exact primeRank_le_one_of_card_dvd_two_prime_squarefree N Nat.prime_three ho hne
        (Nat.prime_iff.mp (by decide : Nat.Prime 13)).squarefree hd'
    · have hc : Nat.Coprime (Nat.card N) (3 ^ 3) :=
        (Nat.prime_three.coprime_iff_not_dvd.mpr h3).symm.pow_right 3
      have hd' : Nat.card N ∣ 2 ^ 11 * 5 ^ 2 * 13 := hc.dvd_mul_left.mp
        (by convert hd using 1; norm_num)
      refine ⟨5,by decide,?_⟩
      intro p hp ho hne
      let : Fact p.Prime := ⟨hp⟩
      exact primeRank_le_one_of_card_dvd_two_prime_squarefree N (by decide : Nat.Prime 5) ho hne
        (Nat.prime_iff.mp (by decide : Nat.Prime 13)).squarefree hd'
  obtain ⟨q,hq,hqr⟩ := hbound
  apply h.normalizes_of_simple_span_odd_ranks hz hq
  intro p hp ho hne
  let : Fact p.Prime := ⟨hp⟩
  rw [←hr p hp ho,primeRank_congr p (e.subgroupMap A)]
  exact (primeRank_mono p hAN).trans (hqr p hp ho hne)

end CFSG.Quasithin.ChapterC.HypothesisC28
