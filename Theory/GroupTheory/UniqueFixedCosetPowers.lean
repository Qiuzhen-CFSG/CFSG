module

public import Theory.GroupTheory.UniqueFixedCosetFusion
import Mathlib.Tactic.Group

/-!
# Unique fixed cosets detected by powers

If a power of an element is conjugate inside M to an element with a unique
fixed coset of M, every conjugator returning the original element to M lies
in M. Every nonidentity element of a finite p-group has a power of order p.
Together these facts extend marked involution fusion control to entire
Sylow factors.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
proof of Lemma 2.5.21, printed p.567.
-/

public section

open Subgroup
namespace UniqueFixedCoset
variable {G : Type*} [Group G]

/-- A marked power detects all returning conjugators of the original element. -/
theorem transporter_mem_of_power {M : Subgroup G} {z x g m : G} {n : ℕ}
    (hzM : z ∈ M) (hu : ∃! q : G ⧸ M, z • q = q)
    (hm : m ∈ M) (hpower : x ^ n = m * z * m⁻¹)
    (hg : g⁻¹ * x * g ∈ M) : g ∈ M := by
  have hp : g⁻¹ * x ^ n * g ∈ M := by
    have he := map_pow (MulAut.conj g⁻¹) x n
    simp only [MulAut.conj_apply, inv_inv] at he
    rw [he]
    exact M.pow_mem hg n
  have hr : (g⁻¹ * m) * z * (g⁻¹ * m)⁻¹ ∈ M := by
    have he : (g⁻¹ * m) * z * (g⁻¹ * m)⁻¹ = g⁻¹ * x ^ n * g := by
      rw [hpower]
      group
    rwa [he]
  have hgm := transporter_mem hzM hu hr
  exact M.inv_mem_iff.mp (by
    simpa only [mul_assoc, mul_inv_cancel, mul_one] using M.mul_mem hgm (M.inv_mem hm))

/-- A nonidentity element of a finite p-subgroup has a power of order p. -/
theorem exists_prime_order_power [Finite G] {p : ℕ} [Fact p.Prime]
    {P : Subgroup G} (hP : IsPGroup p P) {x : G} (hx : x ∈ P) (hx1 : x ≠ 1) :
    ∃ n : ℕ, orderOf (x ^ n) = p := by
  have hd := hP.dvd_orderOf (g := ⟨x, hx⟩) (fun h => hx1 (congrArg Subtype.val h))
  rw [Subgroup.orderOf_mk] at hd
  exact ⟨orderOf x / p, orderOf_pow_orderOf_div (orderOf_pos x).ne' hd⟩

end UniqueFixedCoset

end
