module

public import Theory.GroupAction.BinaryAlternatingFive
public import Theory.GroupAction.FiveOrbitBinaryCoordinates

/-!
# Kernels of alternating pairings under a five-action

Let an order-five group act without fixed points on two elementary binary
groups V and W of order sixteen. For an equivariant alternating symmetric
pairing, any nonzero evaluation at b has kernel precisely the line through b.

Use the first four translates of b as binary coordinates. If u is the pairing
of b with its first translate, equivariance gives the remaining values
u, u·gu·g³u, u·g²u. The fixed-point-free action forces u to be nonidentity;
the binary coordinates of its orbit show these three values are independent.

This refines the commutator calculation in Parrott, *A characterization of the
Tits' simple group* (1972), pp.673–674 and the equality C_J(a)=F on p.678.
-/

open Subgroup
open scoped IsMulCommutative

namespace Theory.GroupAction

private theorem fixed_of_generator {A W : Type*} [Group A] [Finite A] [Group W]
    [MulDistribMulAction A W] (hA : Nat.card A = 5)
    (hfixed : FixedPoints.subgroup A W = ⊥)
    (g : A) (hg : g ≠ 1) (w : W) (hw : g • w = w) : w = 1 := by
  let _ : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  apply hfixed.le
  intro a
  exact (show zpowers g ≤ MulAction.stabilizer A w from zpowers_le.mpr hw)
    (by rw [zpowers_eq_top_of_prime_card hA hg]; trivial)

/-- Each nonzero evaluation of an equivariant alternating pairing has only
its base line in the kernel. -/
public theorem alternating_pairing_kernel_eq_line_of_five {A V W : Type*}
    [Group A] [Finite A] [Group V] [Finite V] [Group W] [Finite W]
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 W]
    [MulDistribMulAction A V] [MulDistribMulAction A W]
    (hA : Nat.card A = 5) (hV : Nat.card V = 16) (hW : Nat.card W = 16)
    (hfixV : FixedPoints.subgroup A V = ⊥)
    (hfixW : FixedPoints.subgroup A W = ⊥)
    (f : V →* (V →* W)) (halt : ∀ x, f x x = 1)
    (hsymm : ∀ x y, f x y = f y x)
    (hequiv : ∀ (a : A) (x y : V), f (a • x) (a • y) = a • f x y)
    (b : V) (hb : b ≠ 1) (hbn : f b ≠ 1) :
    ∀ x, f b x = 1 → x = 1 ∨ x = b := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let _ : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨g, hg⟩ := exists_ne (1 : A)
  obtain ⟨hrel, hcoords⟩ := five_orbit_binary_coordinates hA hV hfixV b hb g hg
  have hsq (w : W) : w * w = 1 := by
    simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 W) w
  have hsq' (w t : W) : w * (w * t) = t := by rw [← mul_assoc, hsq, one_mul]
  have hfix2 (w : W) (hw : g ^ 2 • w = w) : w = 1 := by
    apply fixed_of_generator hA hfixW (g ^ 2) ?_ w hw
    have ho : orderOf g = 5 := orderOf_eq_prime
      (by simpa [hA] using pow_card_eq_one' (x := g)) hg
    intro he
    have hd := orderOf_dvd_of_pow_eq_one he
    rw [ho] at hd
    norm_num at hd
  let u := f b (g • b)
  let v := f b (g ^ 2 • b)
  let w := f b (g ^ 3 • b)
  have h12 : f (g • b) (g ^ 2 • b) = g • u := by
    simpa only [smul_smul, ← pow_two] using hequiv g b (g • b)
  have h13 : f (g • b) (g ^ 3 • b) = g • v := by
    have hh := hequiv g b (g ^ 2 • b)
    rw [smul_smul, show g * g ^ 2 = g ^ 3 by group] at hh
    exact hh
  have h23 : f (g ^ 2 • b) (g ^ 3 • b) = g ^ 2 • u := by
    have hh := hequiv (g ^ 2) b (g • b)
    rw [smul_smul, show g ^ 2 * g = g ^ 3 by group] at hh
    exact hh
  have h24 : g ^ 2 • v = v * (g • u) * (g ^ 2 • u) := by
    have hh := hequiv (g ^ 2) b (g ^ 2 • b)
    have hp : g ^ 2 * g ^ 2 = g ^ 4 := by group
    rw [smul_smul, hp, hrel, map_mul, map_mul, map_mul,
      hsymm (g ^ 2 • b) b, hsymm (g ^ 2 • b) (g • b),
      h12, halt, h23, mul_one] at hh
    exact hh.symm
  have h34 : g ^ 3 • u = w * (g • v) * (g ^ 2 • u) := by
    have hh := hequiv (g ^ 3) b (g • b)
    rw [smul_smul, ← pow_succ, hrel, map_mul, map_mul, map_mul,
      hsymm (g ^ 3 • b) b, hsymm (g ^ 3 • b) (g • b),
      hsymm (g ^ 3 • b) (g ^ 2 • b), h13, h23, halt, mul_one] at hh
    exact hh.symm
  have hg5 : g ^ 5 = 1 := by simpa [hA] using pow_card_eq_one' (x := g)
  have hsum : v = u * (g • u) * (g ^ 3 • u) := by
    have hfix : g ^ 2 • (v * (u * (g • u) * (g ^ 3 • u))) =
        v * (u * (g • u) * (g ^ 3 • u)) := by
      simp only [smul_mul', smul_smul, ← pow_add, hg5, one_smul, h24, show g ^ 2 * g = g ^ 3 by group]
      simp only [mul_assoc, mul_left_comm, mul_comm, hsq']
    have he := hfix2 _ hfix
    exact (eq_inv_of_mul_eq_one_left he).trans (inv_eq_of_mul_eq_one_left (hsq _))
  have hun : u ≠ 1 := by
    intro hu
    have hv : v = 1 := by simp only [hu, smul_one, mul_one] at hsum; exact hsum
    have hw : w = 1 := by simpa only [hu, hv, smul_one, mul_one] using h34.symm
    apply hbn
    apply MonoidHom.ext
    intro x
    obtain ⟨e, rfl⟩ := hcoords.2 x
    change f b _ = 1
    simp only [pow_zero, one_smul, pow_one, map_mul, map_pow, halt, one_pow,
      one_mul, show f b (g • b) = 1 from hu, show f b (g ^ 2 • b) = 1 from hv,
      show f b (g ^ 3 • b) = 1 from hw]
  obtain ⟨hrelW, hcoordsW⟩ := five_orbit_binary_coordinates hA hW hfixW u hun g hg
  have hwformula : w = u * (g ^ 2 • u) := by
    have hh : g ^ 3 • u = w * (g • u) * (g ^ 2 • u) * (g ^ 4 • u) * (g ^ 2 • u) := by
      simpa only [hsum, smul_mul', smul_smul, ← pow_two,
        show g * g ^ 3 = g ^ 4 by group, mul_assoc] using h34
    rw [hrelW] at hh
    simp only [mul_assoc, mul_left_comm, mul_comm, hsq'] at hh
    have he : w * (u * (g ^ 2 • u)) = 1 := by
      apply mul_right_cancel (b := g ^ 3 • u)
      simpa only [one_mul, mul_assoc, mul_left_comm, mul_comm] using hh.symm
    exact (eq_inv_of_mul_eq_one_left he).trans (inv_eq_of_mul_eq_one_left (hsq _))
  intro x hx
  obtain ⟨e, rfl⟩ := hcoords.2 x
  let k : Fin 4 → Fin 2 := ![e 1 + e 2 + e 3, e 2, e 3, e 2]
  have hword : f b ((g ^ 0 • b) ^ (e 0).val * (g ^ 1 • b) ^ (e 1).val *
      (g ^ 2 • b) ^ (e 2).val * (g ^ 3 • b) ^ (e 3).val) =
      (g ^ 0 • u) ^ (k 0).val * (g ^ 1 • u) ^ (k 1).val *
        (g ^ 2 • u) ^ (k 2).val * (g ^ 3 • u) ^ (k 3).val := by
    simp only [map_mul, map_pow, pow_zero, one_smul, pow_one, halt, one_pow,
      one_mul]
    change u ^ (e 1).val * v ^ (e 2).val * w ^ (e 3).val = _
    rw [hsum, hwformula]
    dsimp [k]
    generalize e 1 = e1, e 2 = e2, e 3 = e3
    fin_cases e1 <;> fin_cases e2 <;> fin_cases e3 <;>
      simp [mul_assoc, mul_left_comm, mul_comm, hsq', hsq]
  have hk : k = 0 := hcoordsW.1 (by dsimp only; rw [← hword]; exact hx.trans (by simp))
  have h2 : e 2 = 0 := by simpa [k] using congrFun hk 1
  have h3 : e 3 = 0 := by simpa [k] using congrFun hk 2
  have h1 : e 1 = 0 := by simpa [k, h2, h3] using congrFun hk 0
  have he0 : e 0 = 0 ∨ e 0 = 1 := by omega
  rcases he0 with h0 | h0
  · left; simp [h0, h1, h2, h3]
  · right; simp [h0, h1, h2, h3]

end Theory.GroupAction
