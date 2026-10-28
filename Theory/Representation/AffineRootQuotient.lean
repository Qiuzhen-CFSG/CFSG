module

public import Theory.PGroupCore
public import Mathlib.GroupTheory.Schreier
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.GroupTheory.Rank

/-!
# Rank of an affine root group modulo a two-core

Suppose a parametrized additive field group acts by `1 + t D`. If the
intrinsic two-core is closed under scalar multiples of displacements, the
kernel of its quotient map on this root group is either trivial or the whole
root group. In characteristic two and field size greater than two, its image
therefore cannot have generator rank one.

This elementary conditional reduction is used for Aschbacher--Smith E.1.2(E1)
and the G₂ branch of E.1.14(1), printed pp.210 and 214. The scalar-closure
premise must be proved separately; it is not an axiom or an instance.
-/

public section
open Subgroup

namespace Representation
variable {F X Y V : Type*} [Field F] [Finite F] [CharP F 2]
  [Group X] [Group Y] [Finite Y] [AddCommGroup V] [Module F V]

/-- A full additive field line cannot have rank one modulo the two-core
when the core is closed under scalar multiplication of displacements. The
scalar-closure premise is explicit; no such closure is asserted here. -/
theorem affine_root_quotient_rank_ne_one
    (ρ : X →* Module.End F V)
    (hs : ∀ x y : X, ∀ c : F, y ∈ pCore 2 X →
      ρ x - 1 = c • (ρ y - 1) → x ∈ pCore 2 X)
    (r : Multiplicative F →* X) (D : Module.End F V)
    (hr : ∀ a, ρ (r a) - 1 = a.toAdd • D)
    (q : X →* Y) (hq : q.ker = pCore 2 X) (hF : 2 < Nat.card F) :
    Group.rank (q.comp r).range ≠ 1 := by
  intro hm
  let f := q.comp r
  by_cases hf : Function.Injective f
  · have he := Group.rank_congr (MonoidHom.ofInjective hf)
    have hrank : Group.rank (Multiplicative F) = 1 := he.trans hm
    have hp : ∀ a : Multiplicative F, a ^ 2 = 1 := by
      intro a
      rw [pow_two]
      apply Multiplicative.toAdd.injective
      change a.toAdd + a.toAdd = 0
      exact CharTwo.add_self_eq_zero _
    have hc := card_dvd_exponent_pow_rank' (Multiplicative F) hp
    rw [hrank, pow_one] at hc
    exact (not_le_of_gt hF) (Nat.le_of_dvd (by decide) hc)
  · have hk : f.ker ≠ ⊥ := fun hk => hf (f.ker_eq_bot_iff.mp hk)
    obtain ⟨b, hb, hb1⟩ := f.ker.bot_or_exists_ne_one.resolve_left hk
    have hb0 : b.toAdd ≠ 0 := by
      intro hz
      exact hb1 (Multiplicative.toAdd.injective hz)
    have hbcore : r b ∈ pCore 2 X := by
      rw [← hq]
      exact hb
    have hz : f.range = ⊥ := by
      apply bot_unique
      rintro _ ⟨a, rfl⟩
      have ha := hs (r a) (r b) (a.toAdd / b.toAdd) hbcore (by
        rw [hr, hr, smul_smul, div_mul_cancel₀ _ hb0])
      change q (r a) = 1
      exact show r a ∈ q.ker from hq.symm ▸ ha
    have hm0 : Group.rank f.range = 0 := by
      exact (Group.rank_congr (MulEquiv.subgroupCongr hz)).trans (Group.rank_eq_zero _)
    exact Nat.zero_ne_one (hm0.symm.trans hm)


end Representation
