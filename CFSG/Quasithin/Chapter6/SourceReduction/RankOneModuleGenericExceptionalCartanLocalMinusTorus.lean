module
public import Theory.Representation.BinaryAlternatingSevenControl.CartanNormalizer
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.TraceGeometry.OddClasses
public import Theory.Representation.Mathieu.M24DegreeSpectrum.ElevenTrace.OrderSpectrum
public import Theory.Mathieu.M23.Properties.PointStabilizer


public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalRelocation

/-!
# The inverted minus torus in the centralizing Cartan branch

An odd subgroup normalizing K and inverted modulo a two-group by an
element of K lies inside K: in N(K)/K its squares are both odd and two-power
order. Apply this to the maximal component in the omega-centralizer. The
inverter need not normalize the selected Hall complement upstairs.
The actual two-core quotient preserves the torus order.

The proved carrier calculations restrict a cyclic odd subgroup containing
a cubic to order three in A₇, to three or fifteen in J₂, and to three,
fifteen or twenty-one in M₂₃. The J₂ calculation uses its genuine ATLAS
conjugacy coverage; the M₂₃ calculation uses its actual embedding into M₂₄
and the proved odd-order spectrum. None of the larger orders is 2ᵐ+1.
Consequently the source minus torus forces n=2, and the existing recognition
and relocation prove the full exceptional conclusion.

The torus geometry is explicit here. Deriving it from the original module
alternatives, and constructing the initial component-and-cubic witness,
remain with the local source assembly; no unconditional degree assertion
is made. Source: Aschbacher–Smith 5.1.13, final paragraph, printed p.638,
refs/quasithin.pdf. The imported ATLAS carrier files retain their original
attribution and checked certificates.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalCartanTori
open Sporadic.LeechRelated.J2.TraceGeometry

private theorem order_eq_of_conj {K : Type*} [Group K] {x y : K}
    (h : IsConj x y) : orderOf x = orderOf y := by
  obtain ⟨a,ha⟩ := h
  exact ha.orderOf_eq (a : K)

private theorem janko_odd_power (g : Sporadic.LeechRelated.J2.Carrier)
    (ho : ¬ 2 ∣ orderOf g) : g ^ 15 = 1 ∨ g ^ 7 = 1 := by
  rcases odd_order_conjugacy g ho with ⟨i,j,h⟩ | h | h | h | ⟨i,h⟩
  · left
    have hpow : (x ^ i.val * y ^ j.val) ^ 5 = 1 := by
      rw [((show Commute x y from x_y_commute).pow_pow _ _).mul_pow]
      rw [← pow_mul, Nat.mul_comm i.val 5, pow_mul, x_pow_five, one_pow,
        one_mul, ← pow_mul, Nat.mul_comm j.val 5, pow_mul, y_pow_five, one_pow]
    have hd : orderOf g ∣ 5 := (order_eq_of_conj h).symm ▸ orderOf_dvd_of_pow_eq_one hpow
    exact orderOf_dvd_iff_pow_eq_one.mp (hd.trans (by decide))
  · left
    exact orderOf_dvd_iff_pow_eq_one.mp
      (((order_eq_of_conj h).symm ▸ orderOf_dvd_of_pow_eq_one c_pow_three).trans (by decide))
  · left
    have hp : (r ^ 2) ^ 3 = 1 := by rw [← pow_mul]; exact r_pow_six
    exact orderOf_dvd_iff_pow_eq_one.mp
      (((order_eq_of_conj h).symm ▸ orderOf_dvd_of_pow_eq_one hp).trans (by decide))
  · right
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [order_eq_of_conj h,orderOf_ab]
  · left
    have hp : (c * x ^ i.val) ^ 15 = 1 := by
      rw [((show Commute c x from c_x_commute).pow_right _).mul_pow]
      have hc : c ^ 15 = 1 := by rw [show 15 = 3*5 from rfl,pow_mul,c_pow_three,one_pow]
      have hx : (x ^ i.val) ^ 15 = 1 := by
        rw [←pow_mul,Nat.mul_comm i.val 15,show 15 = 5*3 from rfl,
          Nat.mul_assoc,pow_mul,x_pow_five,one_pow]
      rw [hc,hx,one_mul]
    exact orderOf_dvd_iff_pow_eq_one.mp
      ((order_eq_of_conj h).symm ▸ orderOf_dvd_of_pow_eq_one hp)

/-- Odd cyclic subgroups containing a cubic in the literal Hall--Janko carrier. -/
private theorem janko_card (C : Subgroup Sporadic.LeechRelated.J2.Carrier) [IsCyclic C]
    (ho : Odd (Nat.card C)) (h3 : 3 ∣ Nat.card C) : Nat.card C = 3 ∨ Nat.card C = 15 := by
  obtain ⟨g,hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := C)
  have he : orderOf (g : Sporadic.LeechRelated.J2.Carrier) = Nat.card C :=
    (orderOf_injective C.subtype C.subtype_injective g).trans hg
  have hodd : ¬ 2 ∣ orderOf (g : Sporadic.LeechRelated.J2.Carrier) := by
    rw [he]
    exact fun hh => (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr hh)
  rcases janko_odd_power g hodd with hp | hp
  · have hd : Nat.card C ∣ 15 := he ▸ orderOf_dvd_of_pow_eq_one hp
    have hh : ∀ k ∈ (15 : ℕ).divisors, 3 ∣ k → k = 3 ∨ k = 15 := by decide
    exact hh _ (Nat.mem_divisors.mpr ⟨hd,by decide⟩) h3
  · have hd : 3 ∣ 7 := h3.trans (he ▸ orderOf_dvd_of_pow_eq_one hp)
    norm_num at hd

/-- The concrete point-stabilizer embedding transfers the native M24 spectrum. -/
private theorem mathieu_card (C : Subgroup Sporadic.Mathieu.M23) [IsCyclic C]
    (ho : Odd (Nat.card C)) (h3 : 3 ∣ Nat.card C) :
    Nat.card C = 3 ∨ Nat.card C = 15 ∨ Nat.card C = 21 := by
  let f : Sporadic.Mathieu.M23 →* Sporadic.Mathieu.M24 :=
    (MulAction.stabilizer Sporadic.Mathieu.M24 (24 : Fin 24)).subtype.comp
      Sporadic.Mathieu.m23ToM24PointStabilizer
  have hf : Function.Injective f := Subtype.val_injective.comp
    Sporadic.Mathieu.m23ToM24PointStabilizer_injective
  obtain ⟨g,hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := C)
  have he : orderOf (f g) = Nat.card C :=
    (orderOf_injective (f.comp C.subtype) (hf.comp C.subtype_injective) g).trans hg
  have hodd : ¬ 2 ∣ orderOf (f g) := by
    rw [he]
    exact fun hh => (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr hh)
  have hs := Sporadic.Mathieu.M24OddCyclic.oddOrderSpectrum (f g) hodd
  rw [he] at hs
  rcases hs with hs | hs | hs | hs
  · norm_num [hs] at h3
  · exact .inl ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hs).mp h3).symm
  · exact .inr (.inl hs)
  · exact .inr (.inr hs)

/-- None of the larger cyclic orders is one more than a power of two. -/
private theorem half_degree_one {m r : ℕ}
    (hr : r = 3 ∨ r = 15 ∨ r = 21) (hm : r = 2 ^ m + 1) : m = 1 := by
  have hb : 2 ^ m < 2 ^ 5 := by rcases hr with h | h | h <;> omega
  have hlt : m < 5 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hb
  interval_cases m <;> norm_num at hm <;> omega

/-- The three actual exceptional carriers exclude every larger cubic-containing
cyclic torus of order one more than a power of two. -/
private theorem model_half_degree_one {K : Type*} [Group K] [Finite K]
    (hm : Nonempty (K ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (K ≃* Sporadic.LeechRelated.J2.Carrier) ∨
      Nonempty (K ≃* Sporadic.Mathieu.M23))
    (C : Subgroup K) [IsCyclic C] (ho : Odd (Nat.card C))
    (h3 : 3 ∣ Nat.card C) {m : ℕ} (hc : Nat.card C = 2 ^ m + 1) : m = 1 := by
  apply half_degree_one (r := Nat.card C) ?_ hc
  rcases hm with he | he | he
  all_goals
    obtain ⟨e⟩ := he
    let D := C.map e.toMonoidHom
    have he : Nat.card D = Nat.card C := card_map_of_injective e.injective
    let : IsCyclic D := isCyclic_of_surjective (e.toMonoidHom.subgroupMap C)
      (e.toMonoidHom.subgroupMap_surjective C)
  · exact .inl (he ▸ Representation.BinaryAlternatingSevenControl.Cartan.odd_cyclic_card_three
      D (he.symm ▸ ho) (he.symm ▸ h3))
  · rcases janko_card D (he.symm ▸ ho) (he.symm ▸ h3) with hd | hd
    · exact .inl (he ▸ hd)
    · exact .inr (.inl (he ▸ hd))
  · exact he ▸ mathieu_card D (he.symm ▸ ho) (he.symm ▸ h3)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalCartanTori

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

private theorem odd_inverted_mod_two_le {E P K : Subgroup G} (ho : Odd (Nat.card E))
    (hEN : E ≤ normalizer (K : Set G))
    (hP : IsPGroup 2 P) {t : G} (ht : t ∈ K)
    (hi : ∀ x ∈ E, t*x*t⁻¹*x ∈ P) : E ≤ K := by
  let N := normalizer (K : Set G)
  let R := K.subgroupOf N
  let : R.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let q := QuotientGroup.mk' R
  let Ebar := (E.subgroupOf N).map q
  let Pbar := (P.subgroupOf N).map q
  have he : Nat.card (E.subgroupOf N) = Nat.card E :=
    Nat.card_congr (subgroupOfEquivOfLe hEN).toEquiv
  have heo : Odd (Nat.card Ebar) := (he.symm ▸ ho).of_dvd_nat
    ((E.subgroupOf N).card_map_dvd q)
  have hp : IsPGroup 2 Pbar := hP.comap_subtype.map q
  have hdis : Disjoint Ebar Pbar := by
    obtain ⟨k,hk⟩ := hp.exists_card_eq
    apply disjoint_of_coprime_natCard
    rw [hk]
    exact heo.coprime_two_right.pow_right k
  let tN : N := ⟨t,K.le_normalizer ht⟩
  have htq : q tN = 1 := (QuotientGroup.eq_one_iff tN).mpr ht
  intro x hx
  let xN : N := ⟨x,hEN hx⟩
  have hxe : q xN ∈ Ebar := mem_map_of_mem q hx
  have hs : q xN ^ 2 ∈ Pbar := by
    have hh := mem_map_of_mem q (show tN*xN*tN⁻¹*xN ∈ P.subgroupOf N from hi x hx)
    simpa only [map_mul,map_inv,htq,one_mul,inv_one,mul_one,pow_two] using hh
  have hsq : q xN ^ 2 = 1 := mem_bot.mp (hdis.le_bot ⟨Ebar.pow_mem hxe 2,hs⟩)
  have hval : (⟨q xN,hxe⟩ : Ebar) = 1 :=
    (Nat.Coprime.pow_left_bijective (G := Ebar) heo.coprime_two_right).injective
      (by apply Subtype.ext; change q xN ^ 2 = 1 ^ 2; simpa only [one_pow] using hsq)
  exact (QuotientGroup.eq_one_iff xN).mp (congrArg Subtype.val hval)

/-- An odd torus in the whole omega-centralizer inverted from the original
component modulo the original Sylow lies in the same maximal component,
with its quotient image unchanged in order. -/
theorem localCartan_inverted_torus_placement
    {T : Sylow 2 G} {L W H A B Y X D E : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D)
    (hEA : E ≤ A) (hEC : E ≤ omegaCentralizer T)
    (hinv : ∃ t ∈ (T : Subgroup G) ⊓ X, ∀ e ∈ E, t*e*t⁻¹*e ∈ (T : Subgroup G)) :
    ∃ K : Subgroup G, X ≤ K ∧ K ∈ Chapter1.LStar G (T : Subgroup G) ∧
      LocalCartanWitness T H A (omegaCentralizer T) K D ∧ E ≤ K ∧
      Nat.card ((E.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))) = Nat.card E := by
  obtain ⟨K,hXK,hK,dK,hN,_⟩ := localCartan_centralizer_witness h hH hgen c hY d
  have hoA : Odd (Nat.card A) := by
    rw [←Nat.card_congr (subgroupOfEquivOfLe c.left_le).toEquiv]
    exact OddHall.odd_hall_odd c.left_hall
  have ho : Odd (Nat.card E) := hoA.of_dvd_nat (card_dvd_of_le hEA)
  obtain ⟨t,ht,hi⟩ := hinv
  have hEK : E ≤ K := odd_inverted_mod_two_le ho
    (hEC.trans ((Subgroup.centralizer_le_normalizer _).trans hN))
    T.isPGroup' (hXK ht.2) hi
  refine ⟨K,hXK,hK,dK,hEK,?_⟩
  let q := QuotientGroup.mk' (pCore 2 K)
  let C := E.subgroupOf K
  have hCo : Odd (Nat.card C) := (Nat.card_congr (subgroupOfEquivOfLe hEK).toEquiv).symm ▸ ho
  have hdis : Disjoint C q.ker := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨k,hk⟩ := (pCore_isPGroup (p := 2) (G := K)).exists_card_eq
    apply disjoint_of_coprime_natCard
    rw [hk]
    exact hCo.coprime_two_right.pow_right k
  have hqi : Function.Injective (q.subgroupMap C) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    exact Subtype.ext (mem_bot.mp (hdis.le_bot ⟨x.property,
      congrArg Subtype.val (show q.subgroupMap C x = 1 from hx)⟩))
  exact (Nat.card_congr (MulEquiv.ofBijective (q.subgroupMap C)
    ⟨hqi,q.subgroupMap_surjective C⟩).toEquiv).symm.trans
    (Nat.card_congr (subgroupOfEquivOfLe hEK).toEquiv)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

/-- The postcentralization minus torus forces the original field degree two.
Both its actual placement and inversion modulo T are retained; all three quotient
models are discharged by their proved cyclic order restrictions. -/
theorem localCartan_degree_two_of_minus_torus
    {T : Sylow 2 G} {L W H A B Y X D E : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D)
    (hEA : E ≤ A) (hDE : D ≤ E) (hEC : E ≤ omegaCentralizer T)
    (hcard : Nat.card E = 2 ^ (n / 2) + 1)
    (hinv : ∃ t ∈ (T : Subgroup G) ⊓ X, ∀ e ∈ E, t*e*t⁻¹*e ∈ (T : Subgroup G)) : n = 2 := by
  obtain ⟨K,_,_,dK,hEK,hqcard⟩ := localCartan_inverted_torus_placement
    h hH hgen c hY d hEA hEC hinv
  let C := E.subgroupOf K
  let q := QuotientGroup.mk' (pCore 2 K)
  let : IsCyclic A := (c.left_cyclic_and_card h.sylow_normalizes h.linear).1
  let : IsCyclic E := isCyclic_of_injective (inclusion hEA) (inclusion_injective hEA)
  let : IsCyclic C := isCyclic_of_injective
    (subgroupOfEquivOfLe hEK).toMonoidHom (subgroupOfEquivOfLe hEK).injective
  let : IsCyclic (C.map q) := isCyclic_of_surjective (q.subgroupMap C)
    (q.subgroupMap_surjective C)
  have hoA : Odd (Nat.card A) := by
    rw [←Nat.card_congr (subgroupOfEquivOfLe c.left_le).toEquiv]
    exact OddHall.odd_hall_odd c.left_hall
  have hoE := hoA.of_dvd_nat (card_dvd_of_le hEA)
  have h3 : 3 ∣ Nat.card E := d.cubic_card ▸ card_dvd_of_le hDE
  have hm := LocalCartanTori.model_half_degree_one dK.component_model (C.map q)
    (hqcard.symm ▸ hoE) (hqcard.symm ▸ h3) (hqcard.trans hcard)
  obtain ⟨k,hk⟩ := d.even_exponent h c
  omega

/-- The actual minus torus completes the full exceptional conclusion,
including relocation and recognition of the whole original moved module. -/
theorem localCartan_escape_of_minus_torus
    {T : Sylow 2 G} {L W H A B Y X D E : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D)
    (hEA : E ≤ A) (hDE : D ≤ E) (hEC : E ≤ omegaCentralizer T)
    (hcard : Nat.card E = 2 ^ (n / 2) + 1)
    (hinv : ∃ t ∈ (T : Subgroup G) ⊓ X, ∀ e ∈ E, t*e*t⁻¹*e ∈ (T : Subgroup G)) :
    CartanExceptionalConclusion T L W H := by
  have hn := localCartan_degree_two_of_minus_torus h hH hgen c hY d hEA hDE hEC hcard hinv
  subst n
  exact localCartan_escape_of_witness_degree_two h hH hgen c hY d

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
