module

public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Tactic.NormNum

/-!
# The orbit bound for finite abelian permutation groups

An abelian permutation group embeds into the product of its orbits by evaluation
at one representative of each orbit. Commutativity determines the action at the
other points. The inequality `m ≤ 2^(m-1)` for positive orbit sizes gives the
bound by two to the degree minus the number of orbits.

At equality all orbit sizes are at most two and evaluation is surjective.
The swap on any two-point orbit commutes with the group; matching its values on
representatives therefore realizes that individual swap inside the group.

This is the finite-action argument underlying Aschbacher–Smith,
*The Classification of Quasithin Groups*, B.3.2, printed pp. 83–84.
-/

public section

open scoped BigOperators IsMulCommutative
namespace AbelianPermutation
variable {X : Type*} (A : Subgroup (Equiv.Perm X))

private theorem ext_of_representatives (f g : Equiv.Perm X)
    (hf : ∀ a : A, Commute f a.val) (hg : ∀ a : A, Commute g a.val)
    (h : ∀ q : MulAction.orbitRel.Quotient A X, f q.out = g q.out) : f = g := by
  ext x
  let q : MulAction.orbitRel.Quotient A X := Quotient.mk'' x
  have hx : x ∈ MulAction.orbit A q.out :=
    MulAction.orbitRel_apply.mp (Quotient.exact (Quotient.out_eq q).symm)
  obtain ⟨a, ha⟩ := hx
  change a.val q.out = x at ha
  rw [← ha]
  calc
    f (a.val q.out) = a.val (f q.out) := congrArg (fun e : Equiv.Perm X => e q.out) (hf a).eq
    _ = a.val (g q.out) := congrArg a.val (h q)
    _ = g (a.val q.out) := (congrArg (fun e : Equiv.Perm X => e q.out) (hg a).eq).symm

private noncomputable def orbitEvaluation (a : A) (q : MulAction.orbitRel.Quotient A X) : q.orbit :=
  ⟨a.val q.out, by
    rw [MulAction.orbitRel.Quotient.orbit_eq_orbit_out q Quotient.out_eq']
    exact ⟨a, rfl⟩⟩

variable [IsMulCommutative A]

private theorem orbitEvaluation_injective : Function.Injective (orbitEvaluation A) := by
  intro a b h
  apply Subtype.ext
  apply ext_of_representatives A a.val b.val
  · intro c
    exact congrArg Subtype.val (mul_comm a c)
  · intro c
    exact congrArg Subtype.val (mul_comm b c)
  · intro q
    exact congrArg Subtype.val (congrFun h q)

private theorem succ_le_two_pow (k : ℕ) : k + 1 ≤ 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

private theorem lt_two_pow_of_two_le {k : ℕ} (hk : 2 ≤ k) : k + 1 < 2 ^ k := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction k with
  | zero => norm_num
  | succ k ih => rw [show 2 + (k + 1) = (2 + k) + 1 by omega, pow_succ]; omega

variable [Fintype X]
noncomputable local instance : Fintype (MulAction.orbitRel.Quotient A X) := Fintype.ofFinite _

omit [IsMulCommutative A] in
private theorem card_orbit_pos (q : MulAction.orbitRel.Quotient A X) :
    0 < Nat.card q.orbit := by
  have : Nonempty q.orbit := q.nonempty_orbit.to_subtype
  exact Nat.card_pos

omit [IsMulCommutative A] in
private theorem sum_orbit_sub_one :
    ∑ q : MulAction.orbitRel.Quotient A X, (Nat.card q.orbit - 1) =
      Fintype.card X - Nat.card (MulAction.orbitRel.Quotient A X) := by
  classical
  have hsum : (∑ q : MulAction.orbitRel.Quotient A X, Nat.card q.orbit) = Fintype.card X := by
    simpa only [Nat.card_sigma, Nat.card_eq_fintype_card (α := X)] using
      (Nat.card_congr (MulAction.selfEquivSigmaOrbits' A X)).symm
  rw [Finset.sum_tsub_distrib]
  · rw [hsum]
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
      Nat.card_eq_fintype_card]
  · intro q _
    exact card_orbit_pos A q

private theorem card_le_prod_orbits :
    Nat.card A ≤ ∏ q : MulAction.orbitRel.Quotient A X, Nat.card q.orbit := by
  simpa only [Nat.card_pi] using
    (Nat.card_le_card_of_injective (orbitEvaluation A) (orbitEvaluation_injective A))

omit [IsMulCommutative A] in
private theorem orbit_card_le_pow (q : MulAction.orbitRel.Quotient A X) :
    Nat.card q.orbit ≤ 2 ^ (Nat.card q.orbit - 1) := by
  have hp := card_orbit_pos A q
  have := succ_le_two_pow (Nat.card q.orbit - 1)
  omega

omit [IsMulCommutative A] in
private theorem prod_orbits_le :
    (∏ q : MulAction.orbitRel.Quotient A X, Nat.card q.orbit) ≤
      2 ^ (Fintype.card X - Nat.card (MulAction.orbitRel.Quotient A X)) := by
  calc
    _ ≤ ∏ q : MulAction.orbitRel.Quotient A X, 2 ^ (Nat.card q.orbit - 1) :=
      Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun q _ => orbit_card_le_pow A q)
    _ = _ := by rw [Finset.prod_pow_eq_pow_sum, sum_orbit_sub_one A]

/-- An abelian permutation group is bounded by two to the degree minus the number of orbits. -/
theorem card_le_two_pow_degree_sub_orbits :
    Nat.card A ≤ 2 ^ (Fintype.card X - Nat.card (MulAction.orbitRel.Quotient A X)) :=
  (card_le_prod_orbits A).trans (prod_orbits_le A)

/-- Equality forces small orbits and independent evaluation on their representatives. -/
private theorem small_orbits_and_surjective_of_card_eq
    (h : Nat.card A = 2 ^ (Fintype.card X - Nat.card (MulAction.orbitRel.Quotient A X))) :
    (∀ q : MulAction.orbitRel.Quotient A X, Nat.card q.orbit ≤ 2) ∧
      Function.Surjective (orbitEvaluation A) := by
  have hprod : (∏ q : MulAction.orbitRel.Quotient A X, Nat.card q.orbit) = Nat.card A :=
    le_antisymm (by rw [h]; exact prod_orbits_le A) (card_le_prod_orbits A)
  constructor
  · intro q
    by_contra hq
    have hlt : Nat.card q.orbit < 2 ^ (Nat.card q.orbit - 1) := by
      have := lt_two_pow_of_two_le (k := Nat.card q.orbit - 1) (by omega)
      omega
    have hp := Finset.prod_lt_prod (s := Finset.univ)
      (fun q _ => card_orbit_pos A q) (fun q _ => orbit_card_le_pow A q)
      ⟨q, Finset.mem_univ q, hlt⟩
    rw [Finset.prod_pow_eq_pow_sum, sum_orbit_sub_one A, hprod, h] at hp
    exact (lt_irrefl _ hp)
  · apply ((Nat.bijective_iff_injective_and_card _).mpr
      ⟨orbitEvaluation_injective A, ?_⟩).surjective
    rw [Nat.card_pi]
    exact hprod.symm

/-- At equality each orbit is a singleton or pair and every orbit swap belongs to the group. -/
theorem pair_orbits_of_card_eq [DecidableEq X]
    (h : Nat.card A = 2 ^ (Fintype.card X - Nat.card (MulAction.orbitRel.Quotient A X))) :
    (∀ x : X, Nat.card (MulAction.orbit A x) ≤ 2) ∧
      (∀ x y : X, y ∈ MulAction.orbit A x → Equiv.swap x y ∈ A) := by
  classical
  obtain ⟨hsmall, hsurj⟩ := small_orbits_and_surjective_of_card_eq A h
  have hs (x : X) : Nat.card (MulAction.orbit A x) ≤ 2 := by
    simpa only [MulAction.orbitRel.Quotient.orbit_mk] using hsmall (Quotient.mk'' x)
  refine ⟨hs, ?_⟩
  intro x y hy
  by_cases hxy : x = y
  · subst y
    simpa only [Equiv.swap_self, ← Equiv.Perm.one_def] using A.one_mem
  have horbit : MulAction.orbit A x = {x, y} := by
    refine (Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)).symm
    · intro z hz
      rcases Set.mem_insert_iff.mp hz with rfl | hz
      · exact MulAction.mem_orbit_self _
      · rcases Set.mem_singleton_iff.mp hz with rfl
        exact hy
    · rw [Set.ncard_pair hxy, ← Nat.card_coe_set_eq]
      exact hs x
  have hcomm (a : A) : Commute (Equiv.swap x y) a.val := by
    have hax : a.val x = x ∨ a.val x = y := by
      have hm : a.val x ∈ MulAction.orbit A x := ⟨a, rfl⟩
      simpa only [horbit, Set.mem_insert_iff, Set.mem_singleton_iff] using hm
    have hay : a.val y = x ∨ a.val y = y := by
      obtain ⟨b, hb⟩ := hy
      have hm : a.val y ∈ MulAction.orbit A x := ⟨a * b, by
        change a.val (b.val x) = a.val y
        exact congrArg a.val hb⟩
      simpa only [horbit, Set.mem_insert_iff, Set.mem_singleton_iff] using hm
    have hp : Equiv.swap (a.val x) (a.val y) = Equiv.swap x y := by
      rcases hax with hx | hx <;> rcases hay with hy' | hy'
      · exact False.elim (hxy (a.val.injective (hx.trans hy'.symm)))
      · rw [hx, hy']
      · rw [hx, hy', Equiv.swap_comm]
      · exact False.elim (hxy (a.val.injective (hx.trans hy'.symm)))
    apply Equiv.ext
    intro z
    change Equiv.swap x y (a.val z) = a.val (Equiv.swap x y z)
    rw [a.val.injective.map_swap, hp]
  have hmaps (q : MulAction.orbitRel.Quotient A X) : Equiv.swap x y q.out ∈ q.orbit := by
    have hq : q.out ∈ q.orbit := MulAction.orbitRel.Quotient.mem_orbit.mpr (Quotient.out_eq q)
    by_cases hqx : q.out = x
    · rw [hqx, Equiv.swap_apply_left]
      rw [MulAction.orbitRel.Quotient.orbit_eq_orbit_out q Quotient.out_eq', hqx]
      exact hy
    · by_cases hqy : q.out = y
      · rw [hqy, Equiv.swap_apply_right]
        rw [MulAction.orbitRel.Quotient.orbit_eq_orbit_out q Quotient.out_eq', hqy]
        exact MulAction.mem_orbit_symm.mp hy
      · rwa [Equiv.swap_apply_of_ne_of_ne hqx hqy]
  obtain ⟨a, ha⟩ := hsurj (fun q => ⟨Equiv.swap x y q.out, hmaps q⟩)
  have heq : a.val = Equiv.swap x y := by
    apply ext_of_representatives A a.val (Equiv.swap x y)
    · intro b
      exact congrArg Subtype.val (mul_comm a b)
    · exact hcomm
    · intro q
      exact congrArg Subtype.val (congrFun ha q)
  exact heq ▸ a.property

end AbelianPermutation
