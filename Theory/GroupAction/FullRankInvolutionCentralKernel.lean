module

public import Theory.GroupAction.FourthPowerFixed

/-!
# Commuting automorphisms over a full-rank involution quotient

Suppose an involution acts on an elementary binary quotient W with fixed
subgroup of square-root order. Its fixed subgroup is exactly the image of
the displacement map. If a commuting automorphism acts trivially on the
quotient and on the kernel, and the involution fixes the kernel, it fixes
every fixed point upstairs: lift a displacement expression modulo the
kernel and use commutation to fix the lifted displacement.

This is the linear-algebra step behind the centralization assertion in
Parrott's outer-centralizer calculation (1972, pp.674–676).
-/

namespace MulAut
open Subgroup
open scoped IsMulCommutative

/-- An automorphism trivial on the kernel and quotient fixes the fixed
subgroup of a commuting involution whose quotient displacement has full rank. -/
public theorem fixes_fixedPoints_of_commute_of_full_rank_quotient
    {V W : Type*} [Group V] [IsMulCommutative V]
    [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (q : V →* W) (hq : Function.Surjective q)
    (a b : MulAut V) (c : MulAut W)
    (hcompat : ∀ v : V, q (b v) = c (q v))
    (hc2 : c ^ 2 = 1)
    (hcard : Nat.card W = Nat.card (FixedPoints.subgroup (zpowers c) W) ^ 2)
    (hacomm : Commute a b)
    (haquot : ∀ v : V, q (a v) = q v)
    (haker : ∀ v ∈ q.ker, a v = v)
    (hbker : ∀ v ∈ q.ker, b v = v) :
    ∀ v : V, b v = v → a v = v := by
  let F := FixedPoints.subgroup (zpowers c) W
  let δ : W →* W := {
    toFun := fun w => w⁻¹ * c w
    map_one' := by simp
    map_mul' := by
      intro u v
      simp only [map_mul, mul_inv_rev]
      ac_rfl }
  have hcc (w : W) : c (c w) = w := by
    have hh := congrArg (fun f : MulAut W => f w) hc2
    exact hh
  have hinv (w : W) : w⁻¹ = w := by
    apply inv_eq_of_mul_eq_one_left
    have hh := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 W) w
    simpa only [pow_two] using hh
  have hker : δ.ker = F := by
    ext w
    change w⁻¹ * c w = 1 ↔ w ∈ F
    rw [inv_mul_eq_one]
    exact eq_comm.trans (MulAut.mem_fixed_zpowers_iff c w).symm
  have hrange : δ.range ≤ F := by
    rintro _ ⟨w, rfl⟩
    apply (MulAut.mem_fixed_zpowers_iff c _).mpr
    change c (w⁻¹ * c w) = w⁻¹ * c w
    rw [map_mul, map_inv, hcc, hinv, hinv]
    exact mul_comm _ _
  have heq : δ.range = F := by
    apply eq_of_le_of_card_ge hrange
    have hh := δ.ker.card_mul_index
    rw [index_ker, hker, hcard, pow_two] at hh
    exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos hh).ge
  have hfixδ (u : V) : a (u⁻¹ * b u) = u⁻¹ * b u := by
    have hk : u⁻¹ * a u ∈ q.ker := by
      change q (u⁻¹ * a u) = 1
      rw [map_mul, map_inv, haquot, inv_mul_cancel]
    have hb := hbker _ hk
    have hab : a (b u) = b (a u) := DFunLike.congr_fun hacomm.eq u
    rw [map_mul, map_inv] at hb ⊢
    rw [hab]
    have he : b (a u) = b u * (u⁻¹ * a u) := inv_mul_eq_iff_eq_mul.mp hb
    rw [he]
    calc
      _ = ((a u)⁻¹ * a u) * (u⁻¹ * b u) := by
        simp only [mul_assoc, mul_left_comm, mul_comm]
      _ = _ := by rw [inv_mul_cancel, one_mul]
  intro v hv
  have hqv : q v ∈ F := (MulAut.mem_fixed_zpowers_iff c _).mpr (by
    rw [← hcompat, hv])
  obtain ⟨w, hw⟩ := heq.symm ▸ hqv
  obtain ⟨u, rfl⟩ := hq w
  have hqu : q (u⁻¹ * b u) = q v := by
    rw [map_mul, map_inv, hcompat]
    exact hw
  have hk : (u⁻¹ * b u)⁻¹ * v ∈ q.ker := by
    change q ((u⁻¹ * b u)⁻¹ * v) = 1
    rw [map_mul, map_inv, hqu, inv_mul_cancel]
  have ha := haker _ hk
  rw [map_mul, map_inv, hfixδ] at ha
  exact mul_left_cancel ha

end MulAut
