module

public import Theory.GroupTheory.PGroup.ExponentPrimeRankTwoOrder
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.GroupAction.AutomorphismFixedSubgroup
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# Fixed Frattini sections of odd class-two groups

A finite odd p-group of exponent p, class at most two and prime rank at
most two needs at most two generators. The abelian case follows from prime
rank. In the nonabelian case the existing rank-two order estimate gives
order at most p³, while the nontrivial Frattini subgroup has order at least
p. Burnside's basis theorem therefore gives the same generator bound.

Fixed points of an involution lift through the actual Frattini quotient
by odd-order fixed-point lifting. Applying the preceding generator bound
to the fixed subgroup proves that the fixed quotient has at most p² elements.

This is the fixed-section estimate in Aschbacher–Smith, *The Classification
of Quasithin Groups*, Lemma A.1.28, printed p.26, using the order estimate
from A.1.24. It does not use prime-rank monotonicity for arbitrary quotients.
-/

open Subgroup
open scoped IsMulCommutative commutatorElement

variable {p : ℕ} [Fact p.Prime] {P : Type*} [Group P] [Finite P]

/-- An odd exponent-p group of class at most two and prime rank at most two
has generator rank at most two. -/
public theorem IsPGroup.rank_le_two_of_exponent_prime_class_two
    (hP : IsPGroup p P) (hp : p ≠ 2) (hpow : ∀ x : P, x ^ p = 1)
    (hclass : _root_.commutator P ≤ center P) (hrank : primeRank p P ≤ 2) :
    Group.rank P ≤ 2 := by
  by_cases hab : IsMulCommutative P
  · let : IsMulCommutative P := hab
    have ht := (⊤ : Subgroup P).rank_le_primeRank p (hP.to_subgroup ⊤)
    rw [Group.rank_congr (Subgroup.topEquiv (G := P))] at ht
    exact ht.trans hrank
  have htwo : primeRank p P = 2 := by
    by_contra hn
    have hone : primeRank p P ≤ 1 := by omega
    let : IsCyclic P := hP.isCyclic_of_odd_of_elementary_card_le
      ((Fact.out : p.Prime).odd_of_ne_two hp) (fun E hE => by
        let : IsElementaryAbelian p E := hE
        exact IsElementaryAbelian.card_le_prime_of_primeRank_le_one hone E)
    exact hab inferInstance
  have hnt : Nontrivial P := by
    rcases subsingleton_or_nontrivial P with h | h
    · let : Subsingleton P := h
      exact (hab inferInstance).elim
    · exact h
  let : Nontrivial P := hnt
  have hexp : Monoid.exponent P = p :=
    (Monoid.exponent_eq_prime_iff (Fact.out : p.Prime)).mpr
      (fun x hx => orderOf_eq_prime (hpow x) hx)
  have hcard := hP.card_le_prime_cube_of_exponent_prime_rank_two hp hexp htwo hclass
  let : Fact (IsPGroup p P) := ⟨hP⟩
  have hphi : frattini P ≠ ⊥ := by
    intro he
    apply hab
    apply (_root_.commutator_eq_bot_iff P).mp
    exact bot_unique (he ▸ (commutator_le_frattini_of_isPGroup (p := p)))
  have hphint : Nontrivial (frattini P) := (Subgroup.nontrivial_iff_ne_bot _).mpr hphi
  obtain ⟨n, hn, hncard⟩ := (hP.to_subgroup (frattini P)).nontrivial_iff_card.mp hphint
  have hphicard : p ≤ Nat.card (frattini P) := by
    rw [hncard]
    simpa only [pow_one] using
      (pow_le_pow_right' (Fact.out : p.Prime).one_lt.le (by omega : 1 ≤ n))
  have hqcard : Nat.card (P ⧸ frattini P) ≤ p ^ 2 := by
    have hmul : Nat.card (P ⧸ frattini P) * p ≤ p ^ 2 * p := calc
      _ ≤ Nat.card (P ⧸ frattini P) * Nat.card (frattini P) :=
        Nat.mul_le_mul_left _ hphicard
      _ = Nat.card P := (Subgroup.card_eq_card_quotient_mul_card_subgroup _).symm
      _ ≤ p ^ 2 * p := by simpa only [pow_succ] using hcard
    exact Nat.le_of_mul_le_mul_right hmul (Fact.out : p.Prime).pos
  let : IsElementaryAbelian p (P ⧸ frattini P) := isElementaryAbelian_quotient_frattini
  rw [Group.rank_eq_rank_quotient_frattini P]
  exact IsElementaryAbelian.rank_le_of_card_le _ hqcard

omit [Finite P] in
private theorem class_two_subgroup (hclass : _root_.commutator P ≤ center P)
    (C : Subgroup P) : _root_.commutator C ≤ center C := by
  apply Subgroup.commutator_le.mpr
  intro x _ y _
  apply Subgroup.mem_center_iff.mpr
  intro z
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp
    (hclass (Subgroup.commutator_mem_commutator (mem_top x.val) (mem_top y.val))) z.val

/-- Fixed points of an involution on the Frattini quotient need at most two
generators when the original fixed subgroup has prime rank at most two. -/
public theorem MulAut.rank_fixed_frattini_le_two
    (hP : IsPGroup p P) (hp : p ≠ 2) (hpow : ∀ x : P, x ^ p = 1)
    (hclass : _root_.commutator P ≤ center P) (a : MulAut P) (ha : a ^ 2 = 1)
    (hrank : primeRank p a.fixedSubgroup ≤ 2) :
    Group.rank ((quotientAut (frattini P) a).fixedSubgroup) ≤ 2 := by
  let b := quotientAut (frattini P) a
  let q := QuotientGroup.mk' (frattini P)
  let f : a.fixedSubgroup →* b.fixedSubgroup := {
    toFun := fun x => ⟨q x, by
      apply (MulAut.mem_fixedSubgroup b _).mpr
      change quotientAut (frattini P) a (q x) = q x
      rw [quotientAut_apply_mk, (MulAut.mem_fixedSubgroup a x).mp x.property]⟩
    map_one' := Subtype.ext (map_one q)
    map_mul' := fun x y => Subtype.ext (map_mul q x.val y.val) }
  have hodd : Odd (Nat.card P) := by
    obtain ⟨n, hn⟩ := hP.exists_card_eq
    rw [hn]
    exact ((Fact.out : p.Prime).odd_of_ne_two hp).pow
  have hainv : Function.Involutive a := by
    intro x
    have h := congrArg (fun e : MulAut P => e x) ha
    simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using h
  have hb : b ^ 2 = 1 := by simpa only [b, map_pow, map_one] using congrArg (quotientAut (frattini P)) ha
  have hbinv : Function.Involutive b := by
    intro x
    have h := congrArg (fun e : MulAut (P ⧸ frattini P) => e x) hb
    simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using h
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, hx, he⟩ := MulAut.exists_fixed_preimage_of_odd_card hodd
      (hodd.of_dvd_nat (card_quotient_dvd_card (frattini P))) a b hainv hbinv q
      (QuotientGroup.mk'_surjective _) (fun x => (quotientAut_apply_mk _ _ x).symm)
      y ((MulAut.mem_fixedSubgroup b y).mp y.property)
    exact ⟨⟨x, (MulAut.mem_fixedSubgroup a x).mpr hx⟩, Subtype.ext he⟩
  exact (Group.rank_le_of_surjective f hf).trans
    ((hP.to_subgroup a.fixedSubgroup).rank_le_two_of_exponent_prime_class_two hp
      (fun x => Subtype.ext (hpow x.val)) (class_two_subgroup hclass _) hrank)

/-- The literal fixed subgroup in the Frattini quotient has at most p²
elements under the original fixed-subgroup prime-rank bound. -/
public theorem MulAut.card_fixed_frattini_le_prime_sq
    (hP : IsPGroup p P) (hp : p ≠ 2) (hpow : ∀ x : P, x ^ p = 1)
    (hclass : _root_.commutator P ≤ center P) (a : MulAut P) (ha : a ^ 2 = 1)
    (hrank : primeRank p a.fixedSubgroup ≤ 2) :
    Nat.card ((quotientAut (frattini P) a).fixedSubgroup) ≤ p ^ 2 := by
  let : Fact (IsPGroup p P) := ⟨hP⟩
  let : IsElementaryAbelian p (P ⧸ frattini P) := isElementaryAbelian_quotient_frattini
  let C := (quotientAut (frattini P) a).fixedSubgroup
  have hpowC (x : C) : x ^ p = 1 := by
    apply Subtype.ext
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p (P ⧸ frattini P)) x.val
  have hC := card_dvd_exponent_pow_rank' C hpowC
  exact (Nat.le_of_dvd (pow_pos (Fact.out : p.Prime).pos _) hC).trans
    (pow_le_pow_right' (Fact.out : p.Prime).one_lt.le
      (MulAut.rank_fixed_frattini_le_two hP hp hpow hclass a ha hrank))
