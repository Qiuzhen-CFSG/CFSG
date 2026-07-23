/-
Authors: Tianjiao Nie
-/

module

public import FeitThompson.BGsection1.Defs

namespace PGroup

open scoped Pointwise

section OmegaFrattini

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] [Fact (IsPGroup p G)]

/-- Elements of order `p` lie in `Ω₁(G)`. -/
public theorem mem_omega₁_of_orderOf_eq_p (x : G) (hx : orderOf x = p) :
    x ∈ omega₁ (G := G) (p := p) := by
  let _ := (inferInstance : Finite G)
  let _ := (inferInstance : Fact p.Prime)
  let _ := (inferInstance : Fact (IsPGroup p G))
  change x ∈ Subgroup.closure {y : G | y ^ (p ^ 1) = 1}
  refine Subgroup.subset_closure ?_
  have hxpow : x ^ p = 1 := by simpa [hx] using pow_orderOf_eq_one x
  simpa [pow_one] using hxpow

section Action

variable {A : Type*} [Group A] [MulDistribMulAction A G]

/-- If `A` acts trivially on `Ω₁(G)`, then it fixes every element of order `p`. -/
public theorem fix_order_p_of_actsTriviallyOnSubgroup_omega₁
    (hΩ : ActsTriviallyOnSubgroup (A := A) (G := G) (omega₁ (G := G) (p := p)))
    {x : G} (hx : orderOf x = p) :
    ∀ a : A, a • x = x := by
  intro a
  exact hΩ a x (mem_omega₁_of_orderOf_eq_p (G := G) (p := p) x hx)

/-- If `A` fixes every element of order `p`, then it acts trivially on `Ω₁(G)`. -/
public theorem actsTriviallyOnSubgroup_omega₁_of_fix_order_p
    (hfixp : ∀ x : G, orderOf x = p → ∀ a : A, a • x = x) :
    ActsTriviallyOnSubgroup (A := A) (G := G) (omega₁ (G := G) (p := p)) := by
  let _ := (inferInstance : Finite G)
  let _ := (inferInstance : Fact (IsPGroup p G))
  have hgen_fix : {x : G | x ^ (p ^ 1) = 1} ⊆ fixedPointSubgroup A G := by
    intro x hx
    have hxpow : x ^ p = 1 := by simpa [pow_one] using hx
    by_cases hx1 : x = 1
    · simp [hx1, fixedPointSubgroup]
    · have hx_order_dvd_p : orderOf x ∣ p := (orderOf_dvd_iff_pow_eq_one).2 hxpow
      have hx_order_eq_p : orderOf x = p := by
        rcases (Nat.dvd_prime (Fact.out : Nat.Prime p)).1 hx_order_dvd_p with h1 | hp
        · exfalso
          exact hx1 (orderOf_eq_one_iff.mp h1)
        · exact hp
      exact (FixedPoints.mem_subgroup (M := A) (a := x)).2 (hfixp x hx_order_eq_p)
  have hΩ_le_fixed : omega₁ (G := G) (p := p) ≤ fixedPointSubgroup A G := by
    rw [omega₁, omega]
    exact (Subgroup.closure_le (K := fixedPointSubgroup A G)).2 hgen_fix
  intro a x hx
  have hxfix : x ∈ fixedPointSubgroup A G := hΩ_le_fixed hx
  exact (FixedPoints.mem_subgroup (M := A) (a := x)).1 hxfix a

end Action

/-- In `G ⧸ Φ(G)`, every element of prime order has order `p`. -/
public theorem orderOf_eq_p_of_prime_order_quotient_frattini
    (q : G ⧸ frattini G) (hqprime : Nat.Prime (orderOf q)) :
    orderOf q = p := by
  have hElemQ : IsElementaryAbelian p (G ⧸ frattini G) :=
    isElementaryAbelian_quotient_frattini (R := G) (p := p)
  have hq_pgroup : IsPGroup p (G ⧸ frattini G) :=
    IsElementaryAbelian.isPGroup p (G ⧸ frattini G)
  rcases (IsPGroup.iff_orderOf (p := p) (G := (G ⧸ frattini G))).1 hq_pgroup q with ⟨n, hn⟩
  have hq_dvd_pow : orderOf q ∣ p ^ n := by
    simp [hn]
  have hq_dvd_p : orderOf q ∣ p := hqprime.dvd_of_dvd_pow hq_dvd_pow
  have hpprime : Nat.Prime p := Fact.out
  rcases (Nat.dvd_prime hpprime).1 hq_dvd_p with h1 | hp
  · exact (hqprime.ne_one h1).elim
  · exact hp

/-- The first omega subgroup of `G ⧸ Φ(G)` is the whole quotient. -/
public theorem omega₁_quotient_frattini_eq_top :
    omega₁ (G := G ⧸ frattini G) (p := p) = ⊤ := by
  ext q
  constructor
  · intro _hq
    simp
  · intro _hq
    change q ∈ Subgroup.closure {x : G ⧸ frattini G | x ^ (p ^ 1) = 1}
    refine Subgroup.subset_closure ?_
    have hElem : IsElementaryAbelian p (G ⧸ frattini G) :=
      isElementaryAbelian_quotient_frattini (R := G) (p := p)
    have hpow : q ^ p = 1 := by
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p p (G ⧸ frattini G)) q
    simpa [omega₁, omega, pow_one] using hpow

end OmegaFrattini

end PGroup
