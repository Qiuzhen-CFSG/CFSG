module
public import Theory.GroupAction.SemilinearPointStabilizerExceptional.PrimeReduction.TwoGroupExclusion.Burnside
public import Theory.AtlasPort.OtherSporadic.GroupTheory.CenterSimpleQuotient
public import Theory.GroupTheory.ConjugacyClassSize
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Solvable

/-!
# Solvability of a two-prime subgroup product

A nonabelian simple group whose prime divisors lie in {2,q} has an
involution central in a Sylow two-subgroup. Its conjugacy class has q-power
size, contradicting the proved character-theoretic prime-power class theorem.
Induction through a proper normal subgroup proves solvability. This supplies
solvability of the actual permuting product B S in A.3.15 when B is a q-group;
no normalization of B or S is assumed.

Source: Burnside's two-prime theorem; Aschbacher–Smith A.3.15, pp.50–51.
-/
public section
namespace Theory.GroupTheory
open _root_.MulAction Equiv Subgroup
open scoped Pointwise
/-- A nonabelian simple group cannot have only two and three as prime divisors. -/
private theorem simple_nonabelian_not_only_two_q
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) {q : ℕ} (hq : q.Prime)
    (hprimes : ∀ p : ℕ, p.Prime → p ∣ Nat.card G → p = 2 ∨ p = q) : False := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact (Nat.Prime q) := ⟨hq⟩
  have htwo : 2 ∣ Nat.card G := by
    by_contra htwo
    have hn := Nat.eq_prime_pow_of_unique_prime_dvd (p := q) Nat.card_pos.ne' (by
      intro q hq hqd
      exact (hprimes q hq hqd).resolve_left (by rintro rfl; exact htwo hqd))
    have hG : IsPGroup q G := IsPGroup.of_card hn
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
  have htne : t ≠ 1 := (orderOf_eq_prime_iff.mp htorder).2
  let C : Subgroup G := centralizer {t}
  have hPC : (P : Subgroup G) ≤ C := by
    intro x hx
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val ((mem_center_iff.mp z.property) ⟨x, hx⟩)
  have hCtwo : ¬ 2 ∣ C.index := fun h =>
    P.not_dvd_index (h.trans (index_dvd_of_le hPC))
  have hk := Nat.eq_prime_pow_of_unique_prime_dvd (n := C.index) (p := q)
    C.index_ne_zero_of_finite (by
      intro q hq hqd
      exact (hprimes q hq (hqd.trans C.index_dvd_card)).resolve_left
        (by rintro rfl; exact hCtwo hqd))
  have hc : Nat.card (ConjClasses.mk t).carrier = q ^ C.index.primeFactorsList.length := by
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
  exact hna (IsSimpleGroup.isMulCommutative_of_prime_power_conjClass t htne hq hc)


/-- Burnside solvability for the two-prime support needed by an odd Sylow pair. -/
public theorem isSolvable_of_prime_dvd_card_eq_two_or_prime
    (G : Type*) [Group G] [Finite G] {q : ℕ} (hq : q.Prime)
    (hprimes : ∀ p : ℕ, p.Prime → p ∣ Nat.card G → p = 2 ∨ p = q) :
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
      exact simple_nonabelian_not_only_two_q hna hq hprimes
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
