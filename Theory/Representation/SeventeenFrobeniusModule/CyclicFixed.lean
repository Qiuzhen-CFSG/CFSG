module

public import Theory.Representation.PermutationBasisOrbits
public import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic

/-!
# Fixed coordinates of an eight-cycle

A basis identifies the kernel of an operator minus the identity with coordinate
functions constant on cycles. For the first, second and fourth powers of an
eight-cycle these are exactly functions periodic modulo one, two and four.
Restriction to one period is an explicit linear equivalence, so the dimensions
are valid in characteristic two as well.

This supplies the linear-algebra calculation in Guralnick--Malle,
*Classification of 2F-modules I*, Proposition 4.1, manuscript p.9.
-/

open Module
namespace Representation.SeventeenFrobeniusModule
variable {E V : Type*} [Field E] [AddCommGroup V] [Module E V]

private def cycleFixed (E : Type*) [Field E] (k : ℕ) : Submodule E (Fin 8 → E) where
  carrier := {f | ∀ i, f ((finRotate 8 ^ k) i) = f i}
  zero_mem' := by simp
  add_mem' := by intro f g hf hg i; simp [hf i, hg i]
  smul_mem' := by intro a f hf i; simp [hf i]

private noncomputable def kerCycleEquiv (b : Basis (Fin 8) E V) (T : Module.End E V)
    (k : ℕ) (hT : ∀ i, T (b i) = b ((finRotate 8 ^ k) i)) :
    (T - 1).ker ≃ₗ[E] cycleFixed E k where
  toFun v := ⟨b.equivFun v.val, by
    intro i
    have hv : T v.val = v.val := sub_eq_zero.mp v.property
    rw [← hv]
    have hh := equivariantBasis_equivFun_apply b T (finRotate 8 ^ k) hT v.val i
    rw [hv] at hh
    simpa [hv] using hh⟩
  invFun f := ⟨b.equivFun.symm f.val, by
    change T (b.equivFun.symm f.val) - b.equivFun.symm f.val = 0
    apply sub_eq_zero.mpr
    apply b.equivFun.injective
    funext j
    obtain ⟨i, rfl⟩ := (finRotate 8 ^ k).surjective j
    rw [equivariantBasis_equivFun_apply b T _ hT]
    simp only [LinearEquiv.apply_symm_apply]
    exact (f.property i).symm⟩
  left_inv v := Subtype.ext (b.equivFun.symm_apply_apply v.val)
  right_inv f := Subtype.ext (b.equivFun.apply_symm_apply f.val)
  map_add' v w := by ext; simp
  map_smul' a v := by ext; simp

private theorem cycleFixed_iff (k : ℕ) (hk : k = 1 ∨ k = 2 ∨ k = 4) (f : Fin 8 → E) :
    f ∈ cycleFixed E k ↔ ∀ i : Fin 8, f i = f ⟨i.val % k, by
      have hpos : 0 < k := by omega
      exact (Nat.mod_lt _ hpos).trans_le (by omega)⟩ := by
  change (∀ i, f ((finRotate 8 ^ k) i) = f i) ↔ _
  rcases hk with rfl | rfl | rfl <;>
    simp only [Fin.forall_fin_succ] <;>
    norm_num [pow_succ, Equiv.Perm.mul_apply, finRotate_apply, Fin.add_def, Fin.succ] <;> aesop

private noncomputable def cycleFixedEquiv (k : ℕ) (hk : k = 1 ∨ k = 2 ∨ k = 4) :
    cycleFixed E k ≃ₗ[E] (Fin k → E) where
  toFun f i := f.val ⟨i.val, i.isLt.trans_le (by omega)⟩
  invFun f := ⟨fun i => f ⟨i.val % k, Nat.mod_lt _ (by omega)⟩, by
    rw [cycleFixed_iff k hk]
    intro i
    simp⟩
  left_inv f := by
    ext i
    exact ((cycleFixed_iff k hk f.val).mp f.property i).symm
  right_inv f := by ext i; simp [Nat.mod_eq_of_lt i.isLt]
  map_add' f g := rfl
  map_smul' a f := rfl

private theorem finrank_cycleFixed (k : ℕ) (hk : k = 1 ∨ k = 2 ∨ k = 4) :
    finrank E (cycleFixed E k) = k := by
  rw [(cycleFixedEquiv (E := E) k hk).finrank_eq]
  simp
variable {G : Type*} [Group G]

/-- For a cyclic permutation basis of length eight, these powers have one,
two and four independent fixed coordinates, in every characteristic. -/
public theorem finrank_ker_of_cycle_basis (ρ : Representation E G V) (r : G)
    (b : Basis (Fin 8) E V) (hb : ∀ i, ρ r⁻¹ (b i) = b (finRotate 8 i))
    (k : ℕ) (hk : k = 1 ∨ k = 2 ∨ k = 4) :
    finrank E (ρ (r⁻¹ ^ k) - 1).ker = k := by
  have hp : ∀ n : ℕ, ∀ i, ρ (r⁻¹ ^ n) (b i) = b ((finRotate 8 ^ n) i) := by
    intro n
    induction n with
    | zero => intro i; simp
    | succ n ih =>
      intro i
      rw [pow_succ', map_mul, Module.End.mul_apply, ih, hb,
        pow_succ', Equiv.Perm.mul_apply]
  rw [(kerCycleEquiv b (ρ (r⁻¹ ^ k)) k (hp k)).finrank_eq]
  exact finrank_cycleFixed k hk


end Representation.SeventeenFrobeniusModule
