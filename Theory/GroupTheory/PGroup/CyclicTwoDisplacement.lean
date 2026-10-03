module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Displacement fibers in cyclic two-groups

If an automorphism of a finite cyclic two-group inverts an element of order
four, each square has exactly two preimages under `x ↦ x⁻¹ * a x`. In
particular, the automorphism has exactly two fixed points. No assumption on
the order of the automorphism is needed.

Write the automorphism as the power map with exponent `r`. Inversion on an
element of order four gives `4 ∣ r + 1`, so `r - 1 = 2k` with `k` odd.
Displacement is therefore odd powering, a bijection in a two-group, followed
by squaring. The square kernel in a cyclic group of even order has order two.

This is the cyclic-action calculation for the quaternion–cyclic core in
Janko–Thompson (1970), §4, Case 2, printed p.393. It is independent of any
quaternion coordinates or ambient elementary-rank hypothesis.
-/

namespace IsPGroup

private theorem displacement_power {G : Type*} [Group G] [Finite G] [IsCyclic G]
    (a : MulAut G) (d : G) (hd : orderOf d = 4) (had : a d = d⁻¹) :
    ∃ k : ℕ, Odd k ∧ ∀ x : G, x⁻¹ * a x = (x ^ k) ^ 2 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  obtain ⟨r, hr⟩ := mem_powers_iff_mem_zpowers.mpr (hg (a g))
  have ha (x : G) : a x = x ^ r := by
    obtain ⟨s, rfl⟩ := mem_powers_iff_mem_zpowers.mpr (hg x)
    rw [map_pow, ← hr, ← pow_mul, ← pow_mul, Nat.mul_comm]
  have hdiv : 4 ∣ r + 1 := by
    rw [← hd, orderOf_dvd_iff_pow_eq_one, pow_succ, ← ha, had, inv_mul_cancel]
  obtain ⟨j, hj⟩ := hdiv
  have hjpos : 0 < j := by omega
  refine ⟨2 * (j - 1) + 1, ⟨j - 1, by omega⟩, ?_⟩
  intro x
  have hrj : r = (2 * (j - 1) + 1) * 2 + 1 := by omega
  rw [ha, hrj, pow_succ', inv_mul_cancel_left, pow_mul]

/-- Every square has exactly two preimages under displacement by an automorphism
that inverts an element of order four in a finite cyclic two-group. -/
public theorem card_displacement_fiber_of_inverts_order_four {G : Type*} [Group G] [Finite G] [IsCyclic G]
    (hG : IsPGroup 2 G) (a : MulAut G) (d : G)
    (hd : orderOf d = 4) (had : a d = d⁻¹) (y : G) :
    Nat.card {x : G // x⁻¹ * a x = y ^ 2} = 2 := by
  let : CommGroup G := IsCyclic.commGroup
  obtain ⟨k, hk, he⟩ := displacement_power a d hd had
  let e := hG.powEquiv hk.coprime_two_left
  have he' (x : G) : x⁻¹ * a x = (e x) ^ 2 := he x
  have hcard : Nat.card {x : G // x⁻¹ * a x = y ^ 2} =
      Nat.card (powMonoidHom 2 : G →* G).ker := by
    apply Nat.card_congr
    exact (e.subtypeEquiv (fun x => by simp only [he', Set.mem_preimage,
      Set.mem_singleton_iff, powMonoidHom_apply])).trans
        ((powMonoidHom 2 : G →* G).fiberEquivKer y)
  rw [hcard, IsCyclic.card_powMonoidHom_ker]
  apply Nat.gcd_eq_right
  exact dvd_trans (by norm_num : 2 ∣ 4) (hd ▸ orderOf_dvd_natCard d)

/-- Every square is a displacement if the automorphism inverts an element of
order four in a finite cyclic two-group. -/
public theorem exists_displacement_eq_square_of_inverts_order_four {G : Type*} [Group G] [Finite G] [IsCyclic G]
    (hG : IsPGroup 2 G) (a : MulAut G) (d : G)
    (hd : orderOf d = 4) (had : a d = d⁻¹) (y : G) :
    ∃ x : G, x⁻¹ * a x = y ^ 2 := by
  obtain ⟨k, hk, he⟩ := displacement_power a d hd had
  obtain ⟨x, hx⟩ := (hG.powEquiv hk.coprime_two_left).surjective y
  exact ⟨x, (he x).trans (congrArg (fun z : G => z ^ 2) hx)⟩

/-- An automorphism inverting an element of order four has exactly two fixed
points in a finite cyclic two-group. -/
public theorem card_fixed_of_inverts_order_four
    {G : Type*} [Group G] [Finite G] [IsCyclic G]
    (hG : IsPGroup 2 G) (a : MulAut G) (d : G)
    (hd : orderOf d = 4) (had : a d = d⁻¹) :
    Nat.card {x : G // a x = x} = 2 := by
  calc
    Nat.card {x : G // a x = x} =
        Nat.card {x : G // x⁻¹ * a x = (1 : G) ^ 2} :=
      Nat.card_congr (Equiv.subtypeEquivRight
        (fun x => by rw [one_pow, inv_mul_eq_one]; exact eq_comm))
    _ = 2 := hG.card_displacement_fiber_of_inverts_order_four a d hd had 1

end IsPGroup
