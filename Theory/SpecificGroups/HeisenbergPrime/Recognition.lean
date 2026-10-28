module
public import Theory.SpecificGroups.HeisenbergPrime
public import Theory.GroupTheory.PGroup.PrimeCubeCenter
public import Theory.ElementaryAbelian.ExtraspecialEquiv
import Mathlib.Tactic.Group

/-!
# Recognizing prime Heisenberg groups

Central commutators give a normal multiplication law for x^i y^j c^k.
If x and y do not commute in a group of order p³, their generated subgroup
is the whole group: all proper subgroups have order 1, p, or p² and are
abelian. Evaluation of coordinates is then a surjection between groups
of equal order, hence the required concrete isomorphism.

The normal-form calculation generalizes OrderTwentySevenNormalForm.lean.
Source: Aschbacher–Smith, Lemma A.1.24, printed p.25.
-/

namespace HeisenbergPrime
open scoped commutatorElement
variable {G : Type*} [Group G]

private lemma swap_powers (x y c : G) (hc : c ∈ Subgroup.center G)
    (hs : y * x = c * x * y) (j i : ℕ) :
    y ^ j * x ^ i = c ^ (j * i) * x ^ i * y ^ j := by
  have hcx (n m : ℕ) : Commute (c ^ n) (x ^ m) :=
    (show Commute c x from (Subgroup.mem_center_iff.mp hc x).symm).pow_pow n m
  have hcy (n m : ℕ) : Commute (c ^ n) (y ^ m) :=
    (show Commute c y from (Subgroup.mem_center_iff.mp hc y).symm).pow_pow n m
  have hs1 (j : ℕ) : y ^ j * x = c ^ j * x * y ^ j := by
    induction j with
    | zero => simp
    | succ j ih =>
      calc
        y ^ (j+1) * x = y ^ j * (y * x) := by group
        _ = y ^ j * (c * x * y) := by rw [hs]
        _ = c * (y ^ j * x) * y := by
          have hh := (hcy 1 j).symm.left_comm (x * y)
          simpa only [pow_one, mul_assoc] using hh
        _ = c * (c ^ j * x * y ^ j) * y := by rw [ih]
        _ = c ^ (j+1) * x * y ^ (j+1) := by rw [pow_succ, pow_succ']; group
  induction i with
  | zero => simp
  | succ i ih =>
    calc
      y ^ j * x ^ (i+1) = (y ^ j * x ^ i) * x := by rw [pow_succ, mul_assoc]
      _ = (c ^ (j*i) * x ^ i * y ^ j) * x := by rw [ih]
      _ = c ^ (j*i) * x ^ i * (c ^ j * x * y ^ j) := by simp only [mul_assoc, hs1]
      _ = (c ^ (j*i) * c ^ j) * (x ^ i * x) * y ^ j := by
        simpa only [mul_assoc] using congrArg (fun z => c ^ (j*i) * z)
          ((hcx j i).symm.left_comm (x * y ^ j))
      _ = c ^ (j*(i+1)) * x ^ (i+1) * y ^ j := by rw [← pow_add, ← pow_succ, Nat.mul_add, Nat.mul_one]

private lemma normal_mul (x y c : G) (hc : c ∈ Subgroup.center G)
    (hs : y * x = c * x * y) (i j k l m n : ℕ) :
    (x ^ i * y ^ j * c ^ k) * (x ^ l * y ^ m * c ^ n) =
      x ^ (i+l) * y ^ (j+m) * c ^ (k+n+j*l) := by
  have hcz (a : ℕ) (z : G) : Commute (c ^ a) z :=
    (show Commute c z from (Subgroup.mem_center_iff.mp hc z).symm).pow_left a
  calc
    _ = x ^ i * (y ^ j * x ^ l) * y ^ m * (c ^ k * c ^ n) := by
      rw [mul_assoc (x ^ i * y ^ j)]
      rw [show c ^ k * (x ^ l * y ^ m * c ^ n) =
        (x ^ l * y ^ m) * (c ^ k * c ^ n) by
          rw [← mul_assoc, (hcz k (x ^ l * y ^ m)).eq, mul_assoc]]
      simp only [mul_assoc]
    _ = x ^ i * (c ^ (j*l) * x ^ l * y ^ j) * y ^ m * (c ^ k * c ^ n) := by
      rw [swap_powers x y c hc hs]
    _ = (x ^ i * x ^ l) * (y ^ j * y ^ m) * ((c ^ k * c ^ n) * c ^ (j*l)) := by
      simp only [mul_assoc]
      rw [(hcz (j*l) (x ^ l * (y ^ j * (y ^ m * (c ^ k * c ^ n))))).eq]
      simp only [mul_assoc]
    _ = _ := by simp only [pow_add, mul_assoc]

variable {p : ℕ} [Fact p.Prime]

/-- Evaluate Heisenberg coordinates in a group with the prescribed central relation. -/
@[expose] public def evaluateHom (x y c : G) (hc : c ∈ Subgroup.center G)
    (hs : y * x = c * x * y) (hx : x ^ p = 1) (hy : y ^ p = 1) (hz : c ^ p = 1) :
    HeisenbergPrime p →* G where
  toFun s := x ^ s.b.val * y ^ s.a.val * c ^ s.c.val
  map_one' := by simp
  map_mul' s t := by
    simp only [mul_b, mul_a, mul_c, ZMod.val_add, ZMod.val_mul]
    rw [normal_mul x y c hc hs]
    rw [pow_eq_pow_mod (s.b.val + t.b.val) hx,
      pow_eq_pow_mod (s.a.val + t.a.val) hy,
      pow_eq_pow_mod (s.c.val + t.c.val + s.a.val * t.b.val) hz]
    congr 2
    simp only [Nat.add_mod, Nat.mod_mod]

/-- A noncommuting pair generates every group of prime-cube order. -/
public theorem subgroup_eq_top_of_noncommuting [Finite G]
    (hcard : Nat.card G = p ^ 3) (H : Subgroup G)
    (x y : H) (hxy : x * y ≠ y * x) : H = ⊤ := by
  have hd : Nat.card H ∣ p ^ 3 := hcard ▸ H.card_subgroup_dvd_card
  obtain ⟨k, hk, hH⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hd
  have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hk' with rfl | rfl | rfl | rfl
  · let : IsCyclic H := isCyclic_of_card_dvd_prime (p := p) (by simp [hH])
    exact (hxy (IsMulCommutative.is_comm.comm x y)).elim
  · let : IsCyclic H := isCyclic_of_card_dvd_prime (p := p) (by simp [hH])
    exact (hxy (IsMulCommutative.is_comm.comm x y)).elim
  · let : IsMulCommutative H := IsPGroup.isMulCommutative_of_card_eq_prime_sq hH
    exact (hxy (IsMulCommutative.is_comm.comm x y)).elim
  · exact (Subgroup.card_eq_iff_eq_top H).mp (hH.trans hcard.symm)

/-- A nonabelian exponent-p group of order p³ and class at most two is
isomorphic to the fixed prime Heisenberg group. -/
public theorem nonempty_mulEquiv_of_card_prime_cube [Finite G]
    (hcard : Nat.card G = p ^ 3) (hpow : ∀ g : G, g ^ p = 1)
    (hclass : _root_.commutator G ≤ Subgroup.center G)
    (hncomm : ¬ IsMulCommutative G) : Nonempty (G ≃* HeisenbergPrime p) := by
  classical
  have hpair : ∃ x y : G, x * y ≠ y * x := by
    by_contra h
    push Not at h
    exact hncomm ⟨⟨h⟩⟩
  obtain ⟨x, y, hxy⟩ := hpair
  let c := ⁅y, x⁆
  have hc : c ∈ Subgroup.center G := hclass (Subgroup.commutator_mem_commutator (Subgroup.mem_top y) (Subgroup.mem_top x))
  have hs : y * x = c * x * y := by simp [c, commutatorElement_def, mul_assoc]
  let f := evaluateHom x y c hc hs (hpow x) (hpow y) (hpow c)
  have hx : x ∈ f.range := by
    refine ⟨⟨0, 1, 0⟩, ?_⟩
    simp [f, evaluateHom, ZMod.val_one]
  have hy : y ∈ f.range := by
    refine ⟨⟨1, 0, 0⟩, ?_⟩
    simp [f, evaluateHom, ZMod.val_one]
  have hrange : f.range = ⊤ := subgroup_eq_top_of_noncommuting hcard f.range
    ⟨x, hx⟩ ⟨y, hy⟩ (fun h => hxy (congrArg Subtype.val h))
  have hsurj : Function.Surjective f := MonoidHom.range_eq_top.mp hrange
  exact ⟨(MulEquiv.ofBijective f (hsurj.bijective_of_nat_card_le
    (by rw [card, hcard]))).symm⟩

/-- Recognition also transports extraspeciality to the original group. -/
public theorem isExtraspecial_of_card_prime_cube [Finite G] (hp : p ≠ 2)
    (hcard : Nat.card G = p ^ 3) (hpow : ∀ g : G, g ^ p = 1)
    (hclass : _root_.commutator G ≤ Subgroup.center G)
    (hncomm : ¬ IsMulCommutative G) : IsExtraspecial p G := by
  obtain ⟨e⟩ := nonempty_mulEquiv_of_card_prime_cube hcard hpow hclass hncomm
  exact IsExtraspecial.of_mulEquiv e.symm (isExtraspecial hp)

end HeisenbergPrime
