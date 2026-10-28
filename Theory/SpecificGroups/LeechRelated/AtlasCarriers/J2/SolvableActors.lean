module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.SylowOvergroups.PrimeActors
public import Theory.GroupTheory.Hall.Existence
public import Mathlib.Algebra.Group.PUnit

/-!
# Cyclic odd actors in solvable Hall--Janko Sylow overgroups

Hall existence puts a full Sylow two-subgroup in a three-free Hall subgroup.
The certified two-local cover and the quintic exclusion force that subgroup
to be a two-group. Thus a solvable full-Sylow overgroup has only two and
three in its order. In the first native local its odd part has order three;
in the second, the actual quotient S₃ × C₃ and its two-group kernel exclude
a cyclic nine. The outer two-group theorem gives the same bound in Aut(J₂),
retaining the original cyclic actor and the full inner Sylow.

The consumer is the original escaping Cartan action in Chapter6.
Source: Aschbacher--Smith 5.1.13, printed p.637, refs/quasithin.pdf;
GLS3 Table 5.3g. The imported ATLAS J2G1-p100B0 calculations retain their
source attribution and checked native carriers. No order or simplicity
certification is added here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Sporadic.LeechRelated.J2.SolvableActors
private theorem prime_dvd_card (S : Sylow 2 Carrier) (K : Subgroup Carrier)
    (hSK : (S : Subgroup Carrier) ≤ K) (hs : Group.IsSolvable K)
    (p : ℕ) (hp : p.Prime) (hpk : p ∣ Nat.card K) : p = 2 ∨ p = 3 := by
  classical
  let _ : MulDistribMulAction Unit K := {
    smul _ x := x
    one_smul _ := rfl
    mul_smul _ _ _ := rfl
    smul_one _ := rfl
    smul_mul _ _ _ := rfl }
  let P := S.subtype hSK
  let π : Set Nat.Primes := {q | q.val ≠ 3}
  have hPπ : IsPiSubgroup π (P : Subgroup K) := by
    intro q hq
    obtain ⟨n,hn⟩ := P.isPGroup'.exists_card_eq
    have hq2 := Nat.prime_eq_prime_of_dvd_pow q.property Nat.prime_two (hn ▸ hq)
    change q.val ≠ 3
    omega
  obtain ⟨U,hU,_,hPU⟩ := exists_isHallSubgroup_isInvariant_of_isPiSubgroup
    (A := Unit) hs (by simp) π (P : Subgroup K) hPπ ⟨fun _ _ => Iff.rfl⟩
  have hUS : (S : Subgroup Carrier) ≤ U.map K.subtype := by
    have hh := map_mono (f := K.subtype) hPU
    simpa only [P,Sylow.coe_subtype,map_subgroupOf_eq_of_le hSK] using hh
  have h3 : ¬ 3 ∣ Nat.card U := fun h => hU.p_in_pi_of_p_dvd_card ⟨3,Nat.prime_three⟩ h rfl
  have hUc : Nat.card U ∣ 128 := by
    have h3' : ¬ 3 ∣ Nat.card (U.map K.subtype) := by
      rwa [card_map_of_injective K.subtype_injective]
    have h5 := SylowOvergroups.not_five_of_three_free S (U.map K.subtype) hUS h3'
    have hn : U.map K.subtype ≠ ⊤ := by
      intro he
      apply h3'
      rw [he,card_top,ExceptionalParabolics.FirstParabolic.card_carrier]
      decide
    have hd := SylowOvergroups.proper_overgroup_order S (U.map K.subtype) hUS hn
    rw [card_map_of_injective K.subtype_injective] at hd h5
    have hdiv : ∀ m : ℕ, (m ∣ 1920 ∨ m ∣ 1152) → ¬ 3 ∣ m → ¬ 5 ∣ m → m ∣ 128 := by
      intro m hm h3 h5
      rcases hm with hm | hm
      · have hcop : Nat.Coprime m 15 := by
          rw [show 15 = 3*5 from rfl,Nat.coprime_mul_iff_right]
          exact ⟨(Nat.prime_three.coprime_iff_not_dvd.mpr h3).symm,
            ((by decide : Nat.Prime 5).coprime_iff_not_dvd.mpr h5).symm⟩
        exact hcop.dvd_of_dvd_mul_right hm
      · have hcop : Nat.Coprime m 9 :=
          ((Nat.prime_three.coprime_iff_not_dvd.mpr h3).symm).pow_right 2
        exact hcop.dvd_of_dvd_mul_right hm
    exact hdiv _ hd h3 h5
  by_cases hp3 : p = 3
  · exact Or.inr hp3
  left
  have hi : ¬ p ∣ U.index := fun hi => hU.p_in_pi_of_p_dvd_index ⟨p,hp⟩ hi hp3
  have hpc : p ∣ Nat.card U := (hp.dvd_mul.mp (U.card_mul_index.symm ▸ hpk)).resolve_right hi
  exact Nat.prime_eq_prime_of_dvd_pow hp Nat.prime_two (show p ∣ 2^7 from hpc.trans hUc)

/-- Every odd subgroup of that same overgroup is a three-group. -/
private theorem odd_isPGroup (S : Sylow 2 Carrier) (K D : Subgroup Carrier)
    (hSK : (S : Subgroup Carrier) ≤ K) (hs : Group.IsSolvable K)
    (hDK : D ≤ K) (hodd : Odd (Nat.card D)) : IsPGroup 3 D := by
  have he := Nat.eq_prime_pow_of_unique_prime_dvd (Nat.card_pos (α := D)).ne' (by
    intro p hp hpd
    rcases prime_dvd_card S K hSK hs p hp (hpd.trans (card_dvd_of_le hDK)) with h | h
    · subst p
      exact (hodd.not_two_dvd_nat hpd).elim
    · exact h)
  exact IsPGroup.of_card he


private theorem cyclic_in_second_card_dvd_three
    (D : Subgroup ExceptionalParabolics.Seed.p₂) (ho : Odd (Nat.card D))
    (hc : IsCyclic D) : Nat.card D ∣ 3 := by
  let := hc
  open ExceptionalParabolics ExceptionalParabolics.Seed ExceptionalParabolics.PairNormalizer in
  obtain ⟨e⟩ := p₂_quotient_equiv
  let q := e.toMonoidHom.comp (QuotientGroup.mk' _)
  have hk : IsPGroup 2 q.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    exact ExceptionalParabolics.PairNormalizer.q₂_isPGroup.comap_subtype
  have hi : Function.Injective (q.comp D.subtype) := by
    apply (injective_iff_map_eq_one _).mpr
    intro x hx
    have hd : Disjoint D q.ker := by
      apply disjoint_of_coprime_natCard
      obtain ⟨k,hk⟩ := hk.exists_card_eq
      rw [hk]
      exact ho.coprime_two_right.pow_right k
    exact Subtype.ext (disjoint_def.mp hd x.property hx)
  obtain ⟨d,hd⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := D)
  have hx : orderOf (q d) = Nat.card D := (orderOf_injective (q.comp D.subtype) hi d).trans hd
  have hn : (q d)^3 = 1 := by
    have ho' : Odd (orderOf (q d)) := hx ▸ ho
    have hn : ∀ x : ExceptionalParabolics.PairNormalizer.QuotientModel,
        x^6=1 := by decide +kernel
    have hd : orderOf (q d) ∣ 3 := ho'.coprime_two_right.dvd_of_dvd_mul_left
      (show orderOf (q d) ∣ 2*3 from orderOf_dvd_of_pow_eq_one (hn _))
    exact orderOf_dvd_iff_pow_eq_one.mp hd
  rw [←hx]
  exact orderOf_dvd_of_pow_eq_one hn

/-- Every cyclic odd actor in a solvable full-Sylow overgroup of the actual
Hall--Janko carrier has order dividing three. -/
theorem cyclic_odd_card_dvd_three (S : Sylow 2 Carrier) (K D : Subgroup Carrier)
    (hSK : (S : Subgroup Carrier) ≤ K) (hs : Group.IsSolvable K)
    (hDK : D ≤ K) (ho : Odd (Nat.card D)) (hc : IsCyclic D) : Nat.card D ∣ 3 := by
  let := hs
  let := hc
  have hKt : K ≠ ⊤ := by
    intro ht
    let : Group.IsSolvable Carrier := Group.isSolvable_of_surjective
      (f := K.subtype) (by rw [ht]; exact topEquiv.surjective)
    let : Group.IsPerfect ExceptionalParabolics.Seed.l₁ :=
      ExceptionalParabolics.FirstParabolic.CoverSquareOrbit.l₁_isPerfect
    have hn : Nontrivial ExceptionalParabolics.Seed.l₁ :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [ExceptionalParabolics.FirstParabolic.card_l₁]; decide)
    exact Group.IsPerfect.not_isSolvable ExceptionalParabolics.Seed.l₁ inferInstance
  let S₀ := ExceptionalParabolics.SecondParabolic.sylow ExceptionalParabolics.FirstParabolic.card_l₁
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Carrier S S₀
  let a := MulAut.conj g
  have hS : (S : Subgroup Carrier).map a.toMonoidHom = ExceptionalParabolics.Seed.s :=
    congrArg Sylow.toSubgroup hg
  have hKa : K.map a.toMonoidHom ≠ ⊤ := by
    intro he
    apply hKt
    apply map_injective (f := a.toMonoidHom) a.injective
    rw [he,map_top_of_surjective _ a.surjective]
  have hDa : Nat.card (D.map a.toMonoidHom) = Nat.card D := card_map_of_injective a.injective
  rcases SylowOvergroups.proper_overgroup_le (K.map a.toMonoidHom)
    (hS ▸ map_mono hSK) hKa with hfirst | hsecond
  · have hdiv : Nat.card D ∣ 1920 := by
      rw [←hDa]
      exact (card_dvd_of_le ((map_mono hDK).trans hfirst)).trans
        (ExceptionalParabolics.FirstParabolic.card_l₁ ▸ dvd_refl _)
    obtain ⟨k,hk⟩ := (odd_isPGroup S K D hSK hs hDK ho).exists_card_eq
    have hcop : Nat.Coprime (Nat.card D) 640 := by
      rw [hk]
      exact (by decide : Nat.Coprime 3 640).pow_left k
    exact hcop.dvd_of_dvd_mul_right hdiv
  · let E := (D.map a.toMonoidHom).subgroupOf ExceptionalParabolics.Seed.p₂
    have hle := (map_mono (f := a.toMonoidHom) hDK).trans hsecond
    let b := subgroupOfEquivOfLe hle
    have hE : Nat.card E = Nat.card D := (Nat.card_congr b.toEquiv).trans hDa
    let : IsCyclic (D.map a.toMonoidHom) := isCyclic_of_surjective
      (a.toMonoidHom.subgroupMap D) (a.toMonoidHom.subgroupMap_surjective D)
    have hcE : IsCyclic E := isCyclic_of_injective b.toMonoidHom b.injective
    have hh := cyclic_in_second_card_dvd_three E (hE ▸ ho) hcE
    rwa [hE] at hh

/-- The same bound holds for the original cyclic odd subgroup of the full
J₂ automorphism group, with only the full inner Sylow required. -/
theorem cyclic_odd_aut_card_dvd_three
    (S : Sylow 2 Carrier) (J D : Subgroup (MulAut Carrier))
    (hSJ : (S : Subgroup Carrier).map MulAut.conj ≤ J)
    (hs : Group.IsSolvable J) (hDJ : D ≤ J)
    (ho : Odd (Nat.card D)) (hc : IsCyclic D) : Nat.card D ∣ 3 := by
  let := hs
  let := hc
  let i : Carrier →* MulAut Carrier := MulAut.conj
  have hi : Function.Injective i := conj_injective_of_center_eq_bot OrdinaryLocal.center_eq_bot
  have hDin : D ≤ i.range := by
    let q := QuotientGroup.mk' (MulAut.innerSubgroup Carrier)
    have hod : Odd (Nat.card (D.map q)) := ho.of_dvd_nat (card_map_dvd _ q)
    obtain ⟨k,hk⟩ := (outer_isTwoGroup.to_subgroup (D.map q)).exists_card_eq
    have hk0 : k = 0 := by
      by_contra hk0
      exact hod.not_two_dvd_nat (by rw [hk]; exact dvd_pow_self 2 hk0)
    have hb : D.map q = ⊥ := card_eq_one.mp (by rw [hk,hk0,pow_zero])
    simpa only [q,QuotientGroup.ker_mk'] using (map_eq_bot_iff D).mp hb
  let M := J.comap i
  let E := D.comap i
  have hEm : E.map i = D := map_comap_eq_self hDin
  have hEc : Nat.card E = Nat.card D := by rw [←hEm,card_map_of_injective hi]
  let : Group.IsSolvable M := Group.isSolvable_of_isSolvable_injective
    (f := i.subgroupComap J) (fun x y he => Subtype.ext (hi (congrArg Subtype.val he)))
  have hcE : IsCyclic E := isCyclic_of_injective (i.subgroupComap D)
    (fun x y he => Subtype.ext (hi (congrArg Subtype.val he)))
  have hh := cyclic_odd_card_dvd_three S M E
    (fun x hx => hSJ (mem_map_of_mem i hx)) inferInstance (comap_mono hDJ)
    (hEc ▸ ho) hcE
  rwa [hEc] at hh

end Sporadic.LeechRelated.J2.SolvableActors
