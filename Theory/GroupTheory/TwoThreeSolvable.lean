module

public import BenderSuzuki.SE.Section11Lemma113Isaacs
public import Theory.AtlasPort.OtherSporadic.GroupTheory.CenterSimpleQuotient
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Solvable

/-!
# Solvability when the only prime divisors are two and three

A nonabelian simple group cannot have this prime support. If its order is
odd it is a three-group with nontrivial center. Otherwise an involution in
the center of a Sylow two-subgroup has a conjugacy class of three-power size.
The character-theoretic prime-power involution-class theorem gives a proper
normal kernel modulo which the involution is central, contradicting simplicity.
Induction on the group order then handles a proper nontrivial normal subgroup
and its quotient.

This is the two-and-three specialization of Burnside's two-prime theorem.
The character argument is the proved Isaacs 3.8–3.9 endpoint in
`BenderSuzuki.SE.Section11Lemma113Isaacs`. The simple-group argument is
adapted from the existing private proof in the degree-nine `SevenDivisor`
development; this reusable extension does not import that CFSG consumer.
-/

namespace Theory.GroupTheory
open MulAction Equiv Subgroup BenderSuzuki PFAppendixIII
open scoped Pointwise
/-- Burnside's character kernel rules out a prime-power involution class in a simple group. -/
private theorem simple_involution_class_not_prime_power
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (t : G) (ht : IsInvolution t)
    (p k : ℕ) (hp : p.Prime)
    (hc : Nat.card (ConjClasses.mk t).carrier = p ^ k) : False := by
  classical
  let Z := (ConjClasses.mk t).carrier
  have hz (z : G) : z ∈ Z ↔ IsConj z t := by
    simp [Z, ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]
  have hzconj (x y : G) (hx : x ∈ Z) (hy : y ∈ Z) :
      ∃ w : G, y = rightConjugateElem x w := by
    obtain ⟨w, hw⟩ := isConj_iff.mp (((hz x).mp hx).trans ((hz y).mp hy).symm)
    exact ⟨w⁻¹, by simpa [rightConjugateElem] using hw.symm⟩
  have htZ : t ∈ Z := (hz t).mpr (IsConj.refl t)
  obtain ⟨K, hKlt, hKn, hcentral⟩ := (is1_38_39 (⊤ : Subgroup G) Z p k hp
    ⟨t, htZ⟩ (by simp)
    (by
      intro z hz
      obtain ⟨w, rfl⟩ := hzconj t z htZ hz
      exact isInvolution_rightConjugateElem ht)
    (by
      intro z hzZ w _
      apply (hz _).mpr
      apply IsConj.trans ?_ ((hz z).mp hzZ)
      exact (isConj_iff.mpr ⟨w⁻¹, by simp [rightConjugateElem]⟩ :
        IsConj z (rightConjugateElem z w)).symm)
    (by
      intro x hx y hy
      obtain ⟨w, hw⟩ := hzconj x y hx hy
      exact ⟨w, trivial, hw⟩)
    hc).exists_H
  have hKn' : K.Normal := by
    rw [← normalizer_eq_top_iff]
    exact top_unique ((normal_subgroupOf_iff_le_normalizer le_top).mp hKn)
  have hK : K = ⊥ := hKn'.eq_bot_or_eq_top.resolve_right (ne_of_lt hKlt)
  have htcenter : t ∈ center G := by
    rw [mem_center_iff]
    intro g
    have h := hcentral t htZ g (by trivial)
    rw [hK, mem_bot] at h
    have hc : rightConjugateElem t g = t := mul_inv_eq_one.mp h
    dsimp [rightConjugateElem] at hc
    rw [mul_assoc] at hc
    exact (inv_mul_eq_iff_eq_mul.mp hc).symm
  rw [Atlas.GroupTheory.center_eq_bot_of_simple_nonabelian G hna, mem_bot] at htcenter
  exact ht.ne_one htcenter

/-- A nonabelian simple group cannot have only two and three as prime divisors. -/
private theorem simple_nonabelian_not_only_two_three
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G)
    (hprimes : ∀ p : ℕ, p.Prime → p ∣ Nat.card G → p = 2 ∨ p = 3) : False := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have htwo : 2 ∣ Nat.card G := by
    by_contra htwo
    have hn := Nat.eq_prime_pow_of_unique_prime_dvd (p := 3) Nat.card_pos.ne' (by
      intro q hq hqd
      exact (hprimes q hq hqd).resolve_left (by rintro rfl; exact htwo hqd))
    have hG : IsPGroup 3 G := IsPGroup.of_card hn
    have : Nontrivial (center G) := hG.center_nontrivial
    have hne : center G ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot _).mp this
    exact hne (Atlas.GroupTheory.center_eq_bot_of_simple_nonabelian G hna)
  let P : Sylow 2 G := Classical.choice inferInstance
  have : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot _).mpr (P.ne_bot_of_dvd_card htwo)
  have : Nontrivial (center P) := P.isPGroup'.center_nontrivial
  have hZtwo : 2 ∣ Nat.card (center P) :=
    (P.isPGroup'.to_subgroup (center P)).card_eq_or_dvd.resolve_left
      (Nat.ne_of_gt Finite.one_lt_card)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hZtwo
  let t : G := (z : P)
  have htorder : orderOf t = 2 := by
    rw [show t = ((z : P) : G) from rfl, Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hz
  have ht : IsInvolution t := by
    have h := orderOf_eq_prime_iff.mp htorder
    exact ⟨h.2, h.1⟩
  let C : Subgroup G := centralizer {t}
  have hPC : (P : Subgroup G) ≤ C := by
    intro x hx
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val ((mem_center_iff.mp z.property) ⟨x, hx⟩)
  have hCtwo : ¬ 2 ∣ C.index := fun h =>
    P.not_dvd_index (h.trans (index_dvd_of_le hPC))
  have hk := Nat.eq_prime_pow_of_unique_prime_dvd (n := C.index) (p := 3)
    C.index_ne_zero_of_finite (by
      intro q hq hqd
      exact (hprimes q hq (hqd.trans C.index_dvd_card)).resolve_left
        (by rintro rfl; exact hCtwo hqd))
  have hc : Nat.card (ConjClasses.mk t).carrier = 3 ^ C.index.primeFactorsList.length := by
    rw [← hk]
    change Nat.card (ConjClasses.mk t).carrier = (centralizer {t}).index
    calc
      Nat.card (ConjClasses.mk t).carrier = (stabilizer (ConjAct G) t).index := by
        rw [index_stabilizer, ConjAct.orbit_eq_carrier_conjClasses]
        rfl
      _ = ((stabilizer (ConjAct G) t).comap ConjAct.toConjAct.toMonoidHom).index :=
        ((stabilizer (ConjAct G) t).index_comap_of_surjective
          (f := ConjAct.toConjAct.toMonoidHom) ConjAct.toConjAct.surjective).symm
      _ = (centralizer {t}).index :=
        congrArg Subgroup.index (centralizer_eq_comap_stabilizer t).symm
  exact simple_involution_class_not_prime_power hna t ht 3 _ Nat.prime_three hc


/-- A group with no prime divisors other than two and three is solvable. -/
public theorem isSolvable_of_prime_dvd_card_eq_two_or_three
    (G : Type*) [Group G] [Finite G]
    (hprimes : ∀ p : ℕ, p.Prime → p ∣ Nat.card G → p = 2 ∨ p = 3) :
    Group.IsSolvable G := by
  classical
  induction hn : Nat.card G using Nat.strong_induction_on generalizing G with
  | h n ih =>
    by_cases hsub : Subsingleton G
    · let := hsub
      infer_instance
    let : Nontrivial G := not_subsingleton_iff_nontrivial.mp hsub
    by_cases hsimp : IsSimpleGroup G
    · let := hsimp
      apply IsSimpleGroup.comm_iff_isSolvable.mp
      by_contra hcomm
      have hna : ¬ IsMulCommutative G := fun h => hcomm h.is_comm.comm
      exact simple_nonabelian_not_only_two_three hna hprimes
    · have hex : ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ := by
        by_contra h
        apply hsimp
        refine ⟨fun N hN => ?_⟩
        by_cases hb : N = ⊥
        · exact Or.inl hb
        · exact Or.inr (by_contra fun ht => h ⟨N, hN, hb, ht⟩)
      obtain ⟨N, hN, hbot, htop⟩ := hex
      let := hN
      have hcard : Nat.card N * Nat.card (G ⧸ N) = Nat.card G := N.card_mul_index
      have hNpos : 0 < Nat.card N := Nat.card_pos
      have hQpos : 0 < Nat.card (G ⧸ N) := Nat.card_pos
      have hNbig : 1 < Nat.card N := by
        have : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hbot
        exact Finite.one_lt_card
      have hQbig : 1 < Nat.card (G ⧸ N) := N.one_lt_index_of_ne_top htop
      have hNlt : Nat.card N < n := by nlinarith
      have hQlt : Nat.card (G ⧸ N) < n := by nlinarith
      apply (Group.isSolvable_iff_subgroup_quotient N).mpr
      constructor
      · exact ih _ hNlt N (fun p hp hd => hprimes p hp
          (hd.trans N.card_subgroup_dvd_card)) rfl
      · exact ih _ hQlt (G ⧸ N) (fun p hp hd => hprimes p hp
          (hd.trans N.index_dvd_card)) rfl

end Theory.GroupTheory
