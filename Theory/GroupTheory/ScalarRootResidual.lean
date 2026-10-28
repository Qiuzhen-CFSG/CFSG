module

public import Theory.GroupTheory.PResidual.PrimeTo
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.Ring

/-!
# Scalar root groups in prime-to-p residuals

If a normal subgroup contains an element acting on an additive root group
by a scalar a ≠ 1, it contains that root group: the commutator map on its
parameter is multiplication by a − 1. In particular, a p-element supplies
this containment in O^{p′}. Neither faithfulness of the root map nor a
finite ambient group is needed.

Source: the torus/root-group generation step in Aschbacher–Smith 16.4.8,
combined manuscript of 1 March 2004, printed p.1188.
-/

public section

namespace Subgroup
variable {F D : Type*} [Field F] [Group D]

/-- A nontrivial scalar action makes the entire root group a commutator
with any normal subgroup containing the acting element. -/
theorem scalar_root_le_normal (N : Subgroup D) [N.Normal]
    (f : Multiplicative F →* D) (t : D) (ht : t ∈ N)
    (a : F) (ha : a ≠ 1)
    (hact : ∀ x : F, t * f (Multiplicative.ofAdd x) * t⁻¹ =
      f (Multiplicative.ofAdd (a * x))) : f.range ≤ N := by
  rintro _ ⟨x, rfl⟩
  let y : F := x.toAdd / (a - 1)
  have hmem : t * f (Multiplicative.ofAdd y) * t⁻¹ *
      (f (Multiplicative.ofAdd y))⁻¹ ∈ N := by
    have hh := (inferInstance : N.Normal).conj_mem (t⁻¹) (N.inv_mem ht) (f (Multiplicative.ofAdd y))
    convert N.mul_mem ht hh using 1
    group
  have he : t * f (Multiplicative.ofAdd y) * t⁻¹ *
      (f (Multiplicative.ofAdd y))⁻¹ = f x := by
    rw [hact, ← map_inv, ← map_mul]
    congr 1
    change a * y + -y = x.toAdd
    dsimp [y]
    field_simp [sub_ne_zero.mpr ha]
    ring
  rwa [he] at hmem

/-- A p-element acting by a nontrivial scalar puts the root group in O^{p′}. -/
theorem scalar_root_le_primeToResidual (p : ℕ) (f : Multiplicative F →* D)
    (t : D) {k : ℕ} (ht : t ^ (p ^ k) = 1)
    (a : F) (ha : a ≠ 1)
    (hact : ∀ x : F, t * f (Multiplicative.ofAdd x) * t⁻¹ =
      f (Multiplicative.ofAdd (a * x))) : f.range ≤ primeToResidual p D :=
  scalar_root_le_normal _ f t (mem_primeToResidual_of_pow ht) a ha hact
end Subgroup

