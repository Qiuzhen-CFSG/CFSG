module

public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.BinaryRelators.Normalization
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Tactic.Group
import Mathlib.Tactic.FinCases

/-!
# A centralizer reduction for Held's fifth-power defect

Write `d = [x,y³]` with the source's Magma commutator convention, and put
`t = y³d²`. The elementary dihedral identity `t⁻¹xt = xd⁵` turns the
fifth-power defect into a conjugation defect. Its square is trivial and it
is central, so `t²` and conjugates by `t` of elements centralizing `x` also
centralize `x`.

The nine explicit seeds below, together with the central element `z`, therefore
centralize `x`. Membership of `t` in their generated subgroup would eliminate
the fifth-power defect. That membership is an outstanding certificate problem;
this module proves the reduction and does not assert either remaining relator.
Including `z` ensures that conjugates of the possibly nontrivial central
relators belong to the subgroup used by a coset certificate.

Source: John Bray's ATLAS presentation `HeG1-P1.M`, retained in
`Theory/SpecificGroups/Held/Model/Source/`, especially its subgroup `H`.
No presentation identification or multiplier assertion is used.
-/

namespace Held.CentralCovers.TwoPrimary.BinaryRelators.RemainingDefects
variable {E : Type*} [Group E]

private theorem fifth_conjugation (x q : E) (hx : x ^ 2 = 1) :
    let d := x⁻¹ * q⁻¹ * x * q
    let t := q * d ^ 2
    t⁻¹ * x * t = x * d ^ 5 := by
  have hxx : x * x = 1 := by simpa only [pow_two] using hx
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_left hxx
  dsimp
  simp only [pow_succ, pow_zero, mul_inv_rev, inv_inv, hxi,
    mul_assoc, ← mul_assoc x x, hxx, one_mul]

private theorem conjugation_twice (x t a : E)
    (ha : a ∈ Subgroup.center E) (ha2 : a ^ 2 = 1)
    (ht : t⁻¹ * x * t = x * a) : Commute x (t ^ 2) := by
  have h : (t ^ 2)⁻¹ * x * t ^ 2 = x := by
    calc
      (t ^ 2)⁻¹ * x * t ^ 2 = t⁻¹ * (t⁻¹ * x * t) * t := by
        simp only [pow_two, mul_inv_rev, mul_assoc]
      _ = t⁻¹ * (x * a) * t := by rw [ht]
      _ = (t⁻¹ * x * t) * a := by
        simp only [mul_assoc, ← Subgroup.mem_center_iff.mp ha t]
      _ = x := by rw [ht, mul_assoc, ← pow_two, ha2, mul_one]
  change x * t ^ 2 = t ^ 2 * x
  calc
    x * t ^ 2 = t ^ 2 * ((t ^ 2)⁻¹ * x * t ^ 2) := by group
    _ = t ^ 2 * x := by rw [h]

private theorem commute_conjugate (x t a v : E)
    (ha : a ∈ Subgroup.center E) (ht : t⁻¹ * x * t = x * a)
    (hv : Commute x v) : Commute x (t⁻¹ * v * t) := by
  have hvt : Commute (t⁻¹ * x * t) (t⁻¹ * v * t) := by
    simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv] using
      hv.map (MulAut.conj t⁻¹).toMonoidHom
  rw [ht] at hvt
  change x * (t⁻¹ * v * t) = (t⁻¹ * v * t) * x
  apply mul_right_cancel (b := a)
  calc
    x * (t⁻¹ * v * t) * a = (x * a) * (t⁻¹ * v * t) := by
      rw [mul_assoc x (t⁻¹ * v * t) a,
        Subgroup.mem_center_iff.mp ha (t⁻¹ * v * t), ← mul_assoc]
    _ = (t⁻¹ * v * t) * (x * a) := hvt.eq
    _ = (t⁻¹ * v * t) * x * a := (mul_assoc _ _ _).symm

private theorem commute_half_commutator (x q : E) (hx : x ^ 2 = 1)
    (hc : (x⁻¹ * q⁻¹ * x * q) ^ 6 = 1) :
    Commute x ((x⁻¹ * q⁻¹ * x * q) ^ 3) := by
  let c := x⁻¹ * q⁻¹ * x * q
  have hxx : x * x = 1 := by simpa only [pow_two] using hx
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_left hxx
  have hxc : x * c * x⁻¹ = c⁻¹ := by
    dsimp only [c]
    simp only [mul_inv_rev, inv_inv, hxi, mul_assoc, ← mul_assoc x x, hxx, one_mul]
  have hi : (c ^ 3)⁻¹ = c ^ 3 := inv_eq_of_mul_eq_one_left (by
    rw [← pow_add]; exact hc)
  have hp : x * c ^ 3 * x⁻¹ = c ^ 3 := by
    rw [← conj_pow, hxc, inv_pow, hi]
  exact (mul_inv_eq_iff_eq_mul).mp hp

private theorem inverse_commutator_sixth (x y : E)
    (hc : (x⁻¹ * y⁻¹ * x * y) ^ 6 = 1) :
    (x⁻¹ * (y⁻¹)⁻¹ * x * y⁻¹) ^ 6 = 1 := by
  have he : x⁻¹ * (y⁻¹)⁻¹ * x * y⁻¹ = y * (x⁻¹ * y⁻¹ * x * y)⁻¹ * y⁻¹ := by group
  rw [he, conj_pow, inv_pow, hc, inv_one, mul_one, mul_inv_cancel]

private theorem commute_of_magma_commutator (x w : E)
    (h : x⁻¹ * w⁻¹ * x * w = 1) : Commute x w := by
  change x * w = w * x
  have hs := congrArg (fun q : E => w * x * q) h
  simpa only [mul_assoc, mul_inv_cancel_left, mul_one] using hs


/-- The third generator of the source subgroup `H`. -/
@[expose] public def centralizerWord (x y : E) : E :=
  y ^ 3 * (x⁻¹ * (y ^ 3)⁻¹ * x * y ^ 3) ^ 2

/-- Four source centralizer generators, the square of `t`, and their conjugates by `t`. -/
@[expose] public def centralizerSeed (x y : E) : Fin 9 → E
  | 0 => x
  | 1 => y*x*y*x*y⁻¹*x*y*x*y
  | 2 => (x⁻¹*y⁻¹*x*y) ^ 3
  | 3 => (x⁻¹*(y⁻¹)⁻¹*x*y⁻¹) ^ 3
  | 4 => centralizerWord x y ^ 2
  | 5 => (centralizerWord x y)⁻¹ * x * centralizerWord x y
  | 6 => (centralizerWord x y)⁻¹ * (y*x*y*x*y⁻¹*x*y*x*y) * centralizerWord x y
  | 7 => (centralizerWord x y)⁻¹ * ((x⁻¹*y⁻¹*x*y) ^ 3) * centralizerWord x y
  | 8 => (centralizerWord x y)⁻¹ * ((x⁻¹*(y⁻¹)⁻¹*x*y⁻¹) ^ 3) * centralizerWord x y

/-- The explicit seeds together with the common central defect. -/
@[expose] public def centralizerSpan (z x y : E) : Subgroup E :=
  Subgroup.closure (Set.range (centralizerSeed x y) ∪ {z})

/-- The common central defect belongs to the subgroup used for coset calculations. -/
public theorem centralizerSpan_z_mem (z x y : E) : z ∈ centralizerSpan z x y :=
  Subgroup.subset_closure (Or.inr rfl)

/-- All literal relators give loops at every coset of the proposed subgroup. -/
public theorem relator_conjugate_mem_span (z x y : E) (h : Normalized z x y)
    (g : E) (i : Fin 7) : g * relationWord x y i * g⁻¹ ∈ centralizerSpan z x y := by
  rcases h.defects i with he | he
  · rw [he, mul_one, mul_inv_cancel]
    exact Subgroup.one_mem _
  · rw [he, Subgroup.mem_center_iff.mp h.central g, mul_assoc, mul_inv_cancel, mul_one]
    exact centralizerSpan_z_mem z x y

private theorem seeds_commute (z x y : E) (h : Normalized z x y)
    (h0 : relationWord x y 0 = 1) (h5 : relationWord x y 5 = 1) :
    ∀ i : Fin 9, Commute x (centralizerSeed x y i) := by
  have hw : Commute x (y*x*y*x*y⁻¹*x*y*x*y) :=
    commute_of_magma_commutator _ _ h.long_commutator
  have hc := commute_half_commutator x y h0 h5
  have hci := commute_half_commutator x y⁻¹ h0 (inverse_commutator_sixth x y h5)
  have ha : relationWord x y 4 ∈ Subgroup.center E := by
    rcases h.defects 4 with he | he
    · rw [he]; exact Subgroup.one_mem _
    · rw [he]; exact h.central
  have ha2 : relationWord x y 4 ^ 2 = 1 := by
    rcases h.defects 4 with he | he
    · rw [he, one_pow]
    · rw [he]; exact h.square
  have ht : (centralizerWord x y)⁻¹ * x * centralizerWord x y =
      x * relationWord x y 4 := fifth_conjugation x (y ^ 3) h0
  intro i
  fin_cases i
  · exact Commute.refl x
  · exact hw
  · exact hc
  · exact hci
  · exact conjugation_twice x _ _ ha ha2 ht
  · exact commute_conjugate x _ _ x ha ht (Commute.refl x)
  · exact commute_conjugate x _ _ _ ha ht hw
  · exact commute_conjugate x _ _ _ ha ht hc
  · exact commute_conjugate x _ _ _ ha ht hci

/-- Every element of the proposed subgroup centralizes the involution `x`. -/
public theorem centralizerSpan_le (z x y : E) (h : Normalized z x y)
    (h0 : relationWord x y 0 = 1) (h5 : relationWord x y 5 = 1) :
    centralizerSpan z x y ≤ Subgroup.centralizer {x} := by
  apply (Subgroup.closure_le _).mpr
  rintro a (⟨i, rfl⟩ | ha)
  · exact Subgroup.mem_centralizer_singleton_iff.mpr (seeds_commute z x y h h0 h5 i).symm.eq
  · obtain rfl : a = z := ha
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_center_iff.mp h.central x).symm

/-- A membership certificate for `t` eliminates the fifth-power defect. -/
public theorem fifth_eq_one_of_membership (z x y : E) (h : Normalized z x y)
    (h0 : relationWord x y 0 = 1) (h5 : relationWord x y 5 = 1)
    (ht : centralizerWord x y ∈ centralizerSpan z x y) : relationWord x y 4 = 1 := by
  have hc : Commute (centralizerWord x y) x :=
    Subgroup.mem_centralizer_singleton_iff.mp (centralizerSpan_le z x y h h0 h5 ht)
  have he : (centralizerWord x y)⁻¹ * x * centralizerWord x y =
      x * relationWord x y 4 := fifth_conjugation x (y ^ 3) h0
  have hh : (centralizerWord x y)⁻¹ * x * centralizerWord x y = x := by
    simpa only [inv_inv] using hc.inv_left.mul_inv_cancel
  rw [hh] at he
  exact mul_left_cancel (show x * relationWord x y 4 = x * 1 by simpa only [mul_one] using he.symm)

end Held.CentralCovers.TwoPrimary.BinaryRelators.RemainingDefects
