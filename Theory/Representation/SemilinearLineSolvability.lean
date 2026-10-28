module
public import Theory.SpecificGroups.PSL2.OuterSolvable.FieldAutomorphisms
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Algebra.Group.End

/-!
# Solvability of faithful semilinear actions on a field line

The field automorphism attached to a semilinear actor is unique on a nonzero
one-dimensional space, so it gives a homomorphism to the finite-field
Galois group. Its kernel consists of linear scalar maps and is abelian.
Thus the original faithful action group is solvable.

This is the one-dimensional action used in Aschbacher--Smith, *The
Classification of Quasithin Groups*, 6.1.14(5), printed pp.671--672.
-/

public section
open scoped IsMulCommutative
namespace Representation
variable {F W H : Type*} [Field F] [Finite F]
  [AddCommGroup W] [Module F W] [Group H]

/-- A faithful semilinear action on a line over a finite field is solvable. -/
theorem isSolvable_of_semilinear_line
    (ρ : H →* Multiplicative (AddAut W)) (hρ : Function.Injective ρ)
    (hd : Module.finrank F W = 1)
    (hs : ∀ h : H, ∃ σ : F ≃+* F, ∀ c v,
      (ρ h).toAdd (c • v) = σ c • (ρ h).toAdd v) :
    Group.IsSolvable H := by
  classical
  have : Nontrivial W := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank F W)
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  choose σ hσ using hs
  have hn (h : H) : (ρ h).toAdd w ≠ 0 := by
    simpa only [map_zero] using (ρ h).toAdd.injective.ne hw
  have unique (h : H) (τ : F ≃+* F)
      (ht : ∀ c v, (ρ h).toAdd (c • v) = τ c • (ρ h).toAdd v) : σ h = τ := by
    ext c
    exact (smul_left_injective F (hn h)) ((hσ h c w).symm.trans (ht c w))
  let q : H →* (F ≃+* F) := {
    toFun := σ
    map_one' := unique 1 1 (by intro c v; simp)
    map_mul' := fun a b => unique (a * b) (σ a * σ b) (by
      intro c v
      rw [map_mul]
      change (ρ a).toAdd ((ρ b).toAdd (c • v)) =
        σ a (σ b c) • (ρ a).toAdd ((ρ b).toAdd v)
      rw [hσ b, hσ a]) }
  have hlinear (a : q.ker) (c : F) (v : W) :
      (ρ (a : H)).toAdd (c • v) = c • (ρ (a : H)).toAdd v := by
    have ha : σ (a : H) = 1 := a.property
    rw [hσ, ha]
    rfl
  have hcomm (a b : q.ker) : a * b = b * a := by
    apply Subtype.ext
    apply hρ
    apply Multiplicative.toAdd.injective
    apply AddEquiv.ext
    intro v
    obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' w hw).mp hd v
    obtain ⟨d, hdw⟩ := (finrank_eq_one_iff_of_nonzero' w hw).mp hd ((ρ (a : H)).toAdd w)
    obtain ⟨e, hew⟩ := (finrank_eq_one_iff_of_nonzero' w hw).mp hd ((ρ (b : H)).toAdd w)
    change (ρ ((a : H) * (b : H))).toAdd (c • w) =
      (ρ ((b : H) * (a : H))).toAdd (c • w)
    simp only [map_mul]
    change (ρ (a : H)).toAdd ((ρ (b : H)).toAdd (c • w)) =
      (ρ (b : H)).toAdd ((ρ (a : H)).toAdd (c • w))
    simp only [hlinear]
    rw [← hdw, ← hew, hlinear, hlinear, ← hdw, ← hew]
    simp only [smul_smul, mul_comm d e]
  let : IsMulCommutative q.ker := ⟨⟨hcomm⟩⟩
  let : Group.IsSolvable q.ker := inferInstance
  let : Group.IsSolvable (F ≃+* F) := Theory.PSL2.OuterSolvable.finiteFieldAut_isSolvable
  exact Group.isSolvable_of_ker_le_range q.ker.subtype q (by simp)

end Representation
