module

public import Theory.GroupTheory.PGroup.ClassTwoThreeInvolutionExponent
public import Theory.GroupTheory.PGroup.TransitiveInvolutions
public import Theory.GroupTheory.PGroup.ClassTwoCyclicCenter
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.GroupTheory.PGroup.CentralQuotientEightOddAutomorphisms
public import Theory.GroupTheory.PGroup.CentralQuotientFourQuaternionLifts

/-!
# Odd automorphisms with nonelementary center and a small central quotient

For a nonabelian finite two-group with elementary binary central quotient,
three central involutions, and nonelementary center, involutions cannot be
transitive under automorphisms. Otherwise the class-two exponent reduction
and the special-group theorem would make the center elementary.

An odd actor on three points is either trivial or transitive. Thus odd
actors fix every involution. On the abelian center, induction through
successive squares makes such an actor trivial. If the full automorphism
group is not a two-group, Cauchy's theorem and the paired-action kernel
supply an odd-prime actor fixing the center pointwise and acting nontrivially
on the central quotient.

A bound of eight on the central quotient leaves orders four and eight:
orders one and two would make the quotient cyclic and the group abelian.
The invariant commutator pairing excludes a nontrivial center-fixed odd action
in order eight. In order four, the actor cycles the nonidentity quotient
elements, and correcting lifts by central elements gives quaternion relations.
The final theorem assembles these steps, keeping the quotient bound explicit.

Source motivation: MacWilliams, *On 2-groups with no normal abelian
subgroups of rank 3, and their occurrence as Sylow 2-subgroups of finite
simple groups*, Trans. Amer. Math. Soc. 150 (1970), §3, pp. 366–374.
-/

open Subgroup
open scoped IsMulCommutative

namespace IsPGroup

/-- A nonelementary center rules out transitivity on three central involutions
when the central quotient is elementary binary. -/
public theorem not_transitive_involutions_of_nonelementary_center_of_class_two
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hnonab : ¬ IsMulCommutative P)
    (hquot : IsElementaryAbelian 2 (P ⧸ center P))
    (hcentral : ∀ x : P, x ^ 2 = 1 → x ∈ center P)
    (hthree : Nat.card {x : P // orderOf x = 2} = 3)
    (hbad : ¬ IsElementaryAbelian 2 (center P)) :
    ¬ (∀ x y : P, orderOf x = 2 → orderOf y = 2 → ∃ a : MulAut P, a x = y) := by
  intro htrans
  exact hbad (hP.special_of_exponent_four_of_transitive_involutions hnonab hcentral htrans
    (hP.exponent_four_of_class_two_of_transitive_three_involutions hnonab hcentral
      hthree htrans hquot.commutator_le_center_of_central_quotient)).2.2.1

private def involutionPermHom (P : Type*) [Group P] :
    MulAut P →* Equiv.Perm {x : P // orderOf x = 2} where
  toFun a := Equiv.Perm.subtypePerm a.toEquiv (fun x => by
    change orderOf (a x) = 2 ↔ orderOf x = 2
    rw [a.orderOf_eq])
  map_one' := by ext x; rfl
  map_mul' a b := by ext x; rfl

private theorem perm_three_square_or_transitive :
    ∀ a : Equiv.Perm (Fin 3), a ^ 2 = 1 ∨
      ∀ x y : Fin 3, ∃ n : Fin 3, (a ^ n.val) x = y := by
  decide +kernel

private theorem fixes_involutions_of_odd_pow_of_not_transitive
    {P : Type*} [Group P] [Finite P]
    (hthree : Nat.card {x : P // orderOf x = 2} = 3)
    (hnot : ¬ (∀ x y : P, orderOf x = 2 → orderOf y = 2 → ∃ a : MulAut P, a x = y))
    (a : MulAut P) {q : ℕ} (hq : Odd q) (ha : a ^ q = 1) :
    ∀ x : P, orderOf x = 2 → a x = x := by
  classical
  let I := {x : P // orderOf x = 2}
  let : Fintype I := Fintype.ofFinite I
  let e : I ≃ Fin 3 := Fintype.equivFinOfCardEq
    (by simpa only [Nat.card_eq_fintype_card] using hthree)
  let f : MulAut P →* Equiv.Perm (Fin 3) :=
    e.permCongrHom.toMonoidHom.comp (involutionPermHom P)
  have hf (b : MulAut P) (x : I) : f b (e x) = e ⟨b x, (b.orderOf_eq x).trans x.property⟩ := by
    simp [f, involutionPermHom]
    rfl
  rcases perm_three_square_or_transitive (f a) with hs | ht
  · have hp : (f a) ^ q = 1 := by rw [← map_pow, ha, map_one]
    obtain ⟨k, hk⟩ := hq
    have hfa : f a = 1 := by
      rw [hk, pow_add, pow_mul, hs, one_pow, one_mul, pow_one] at hp
      exact hp
    intro x hx
    have he := hf a ⟨x, hx⟩
    rw [hfa] at he
    exact (congrArg Subtype.val (e.injective he)).symm
  · exfalso
    apply hnot
    intro x y hx hy
    obtain ⟨n, hn⟩ := ht (e ⟨x, hx⟩) (e ⟨y, hy⟩)
    refine ⟨a ^ n.val, ?_⟩
    rw [← map_pow, hf] at hn
    exact congrArg Subtype.val (e.injective hn)

/-- Induction on the two-power order proves faithfulness on involutions for odd actors. -/
private theorem abelian_aut_eq_one_of_odd_pow_of_fixes_involutions
    {A : Type*} [Group A] [IsMulCommutative A] (hA : IsPGroup 2 A)
    (a : MulAut A) {q : ℕ} (hq : Odd q) (ha : a ^ q = 1)
    (hfix : ∀ x : A, x ^ 2 = 1 → a x = x) : a = 1 := by
  let : CommGroup A := IsMulCommutative.instCommGroup
  have hind : ∀ k : ℕ, ∀ x : A, x ^ (2 ^ k) = 1 → a x = x := by
    intro k
    induction k with
    | zero =>
      intro x hx
      simp only [pow_zero, pow_one] at hx
      simp [hx]
    | succ k ih =>
      intro x hx
      have hs : a (x ^ 2) = x ^ 2 := ih (x ^ 2) (by
        rw [← pow_mul]
        simpa only [Nat.pow_succ'] using hx)
      let d := a x * x⁻¹
      have hd : d ^ 2 = 1 := by
        dsimp [d]
        rw [mul_pow, inv_pow, ← map_pow, hs, mul_inv_cancel]
      have had : a d = d := hfix d hd
      have hax : a x = d * x := by simp [d]
      have hn : ∀ n : ℕ, (a ^ n) x = d ^ n * x := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
          rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, had, hax]
          rw [pow_succ]
          ac_rfl
      have hdq : d ^ q = 1 := by
        have he := hn q
        rw [ha] at he
        simpa using (mul_right_cancel (show 1 * x = d ^ q * x from by simpa using he)).symm
      obtain ⟨m, hm⟩ := hq
      rw [hm, pow_add, pow_mul, hd, one_pow, one_mul, pow_one] at hdq
      simpa only [hdq, one_mul] using hax
  apply MulEquiv.ext
  intro x
  obtain ⟨k, hk⟩ := hA x
  exact hind k x hk


private theorem fixes_center_of_odd_pow_of_not_transitive_involutions
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hthree : Nat.card {x : P // orderOf x = 2} = 3)
    (hnot : ¬ (∀ x y : P, orderOf x = 2 → orderOf y = 2 → ∃ a : MulAut P, a x = y))
    (a : MulAut P) {q : ℕ} (hq : Odd q) (ha : a ^ q = 1) :
    ∀ z : center P, a z = z := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfix := fixes_involutions_of_odd_pow_of_not_transitive hthree hnot a hq ha
  let r := MulAut.characteristic (center P)
  have hr : r a = 1 := (hP.to_subgroup (center P)).abelian_aut_eq_one_of_odd_pow_of_fixes_involutions (r a) hq
    (by rw [← map_pow, ha, map_one]) (by
      intro z hz
      apply Subtype.ext
      change a z = z
      by_cases he : (z : P) = 1
      · simp [he]
      · exact hfix z (orderOf_eq_prime (congrArg Subtype.val hz) he))
  intro z
  exact congrArg Subtype.val (DFunLike.congr_fun hr z)

/-- A non-two-group automorphism group supplies an odd-prime automorphism
fixing the center pointwise and acting nontrivially on the central quotient. -/
public theorem exists_odd_prime_center_fixed_automorphism_of_nonelementary_center
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hnonab : ¬ IsMulCommutative P)
    (hquot : IsElementaryAbelian 2 (P ⧸ center P))
    (hcentral : ∀ x : P, x ^ 2 = 1 → x ∈ center P)
    (hthree : Nat.card {x : P // orderOf x = 2} = 3)
    (hbad : ¬ IsElementaryAbelian 2 (center P))
    (hAut : ¬ IsPGroup 2 (MulAut P)) :
    ∃ (q : ℕ) (a : MulAut P), q.Prime ∧ Odd q ∧ orderOf a = q ∧
      (∀ z : center P, a z = z) ∧ quotientAut (center P) a ≠ 1 := by
  classical
  have hn : ¬ (Nat.card (MulAut P)).primeFactors ⊆ Nat.primeFactors 2 :=
    fun hs => hAut ((isPGroup_iff_primeFactors_card_subset (by decide)).mpr hs)
  obtain ⟨q, hq, hqn⟩ := Finset.not_subset.mp hn
  obtain ⟨hprime, hdvd, _⟩ := Nat.mem_primeFactors.mp hq
  have hqne : q ≠ 2 := by
    intro he
    subst q
    exact hqn (Nat.mem_primeFactors.mpr ⟨Nat.prime_two, dvd_rfl, by decide⟩)
  have hodd := hprime.eq_two_or_odd'.resolve_left hqne
  let : Fact q.Prime := ⟨hprime⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := MulAut P) q hdvd
  have hapow : a ^ q = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have hnot := hP.not_transitive_involutions_of_nonelementary_center_of_class_two hnonab hquot hcentral hthree hbad
  have hfix := hP.fixes_center_of_odd_pow_of_not_transitive_involutions hthree hnot a hodd hapow
  refine ⟨q, a, hprime, hodd, ha, hfix, ?_⟩
  intro htriv
  have hpair : a ∈ (automorphismPair (center P)).ker := by
    change automorphismPair (center P) a = 1
    rw [automorphismPair_apply]
    apply Prod.ext
    · apply MulEquiv.ext
      intro z
      exact Subtype.ext (hfix z)
    · exact htriv
  let b : (automorphismPair (center P)).ker := ⟨a, hpair⟩
  have hb : b ≠ 1 := by
    intro hb
    have he : a = 1 := congrArg Subtype.val hb
    have heq : q = 1 := by simpa [he] using ha.symm
    exact hprime.ne_one heq
  have hd : 2 ∣ orderOf b :=
    (isPGroup_automorphism_pair_kernel (center P) (hP.to_subgroup _)).dvd_orderOf hb
  have hord : orderOf b = q := (orderOf_coe b).symm.trans ha
  rw [hord] at hd
  exact hqne ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hprime).mp hd).symm


/-- A nonabelian finite two-group with central quotient of order at most eight
has central quotient of order four or eight. -/
public theorem card_center_quotient_eq_four_or_eight_of_le_eight
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hnonab : ¬ IsMulCommutative P)
    (hbound : Nat.card (P ⧸ center P) ≤ 8) :
    Nat.card (P ⧸ center P) = 4 ∨ Nat.card (P ⧸ center P) = 8 := by
  obtain ⟨n, hn⟩ := (hP.to_quotient (center P)).exists_card_eq
  have hnle : n ≤ 3 := by
    by_contra h
    have hh := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 4 ≤ n)
    rw [← hn] at hh
    omega
  have hnlt : ¬ n ≤ 1 := by
    intro h
    have hdvd : Nat.card (P ⧸ center P) ∣ 2 := by
      rw [hn]
      interval_cases n <;> norm_num
    let : IsCyclic (P ⧸ center P) := isCyclic_of_card_dvd_prime (p := 2) hdvd
    exact hnonab (isMulCommutative_of_isCyclic_quotient_center_self P)
  have : n = 2 ∨ n = 3 := by omega
  rcases this with rfl | rfl
  · exact Or.inl hn
  · exact Or.inr hn

/-- With an explicit bound of eight on the central quotient, a nonelementary
center and a non-two-group automorphism group force a central quotient of
order four and elements satisfying the quaternion relations. -/
public theorem exists_quaternion_lifts_of_nonelementary_center_of_quotient_card_le_eight
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hnonab : ¬ IsMulCommutative P)
    (hquot : IsElementaryAbelian 2 (P ⧸ center P))
    (hcentral : ∀ x : P, x ^ 2 = 1 → x ∈ center P)
    (hthree : Nat.card {x : P // orderOf x = 2} = 3)
    (hbad : ¬ IsElementaryAbelian 2 (center P))
    (hAut : ¬ IsPGroup 2 (MulAut P))
    (hbound : Nat.card (P ⧸ center P) ≤ 8) :
    Nat.card (P ⧸ center P) = 4 ∧
      ∃ c d : P, orderOf c = 4 ∧ d ^ 2 = c ^ 2 ∧ d * c * d⁻¹ = c⁻¹ := by
  obtain ⟨q, a, hq, hodd, ha, hfix, hmove⟩ :=
    hP.exists_odd_prime_center_fixed_automorphism_of_nonelementary_center
      hnonab hquot hcentral hthree hbad hAut
  have hfour : Nat.card (P ⧸ center P) = 4 := by
    rcases hP.card_center_quotient_eq_four_or_eight_of_le_eight hnonab hbound with h | h
    · exact h
    · exact (hmove (hquot.quotientAut_eq_one_of_card_eight_of_odd_prime
        h hq hodd a ha hfix)).elim
  exact ⟨hfour, hP.exists_quaternion_lifts_of_center_quotient_card_four
    hnonab hquot hcentral hfour q hq hodd a ha hfix hmove⟩

end IsPGroup
