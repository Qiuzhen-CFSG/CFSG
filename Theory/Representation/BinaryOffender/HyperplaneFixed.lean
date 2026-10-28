module

public import Theory.Representation.BinaryOffender.Defs
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Sylow fixed vectors and invariant binary functionals

If a binary invariant functional vanishes on the full fixed space, it also
vanishes on the fixed space of a Sylow two-subgroup. The orbit of a Sylow-fixed
vector has odd size. Summing its distinct orbit vectors gives a full-group fixed
vector with the same nonzero functional value.

This relative averaging argument is used in the determinant hyperplane
calculation for Aschbacher–Smith, 9.2.3 (1 March 2004 manuscript).
-/

public noncomputable section

namespace Representation.BinaryOffender

/-- An invariant binary functional cannot detect a Sylow-fixed vector unless
it detects a vector fixed by the full group. -/
theorem sylow_fixedSpace_le_ker_of_invariant
    {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (f : V →ₗ[ZMod 2] ZMod 2)
    (hf : ∀ g x, f (ρ g x) = f x)
    (hfix : Representation.invariants ρ ≤ f.ker) (P : Sylow 2 G) :
    fixedSpace ρ (P : Subgroup G) ≤ f.ker := by
  classical
  let : MulAction G V := {
    smul := fun g w => ρ g w
    one_smul := by intro w; change ρ 1 w = w; simp
    mul_smul := by intro g h w; change ρ (g * h) w = ρ g (ρ h w); simp }
  intro x hx
  have hP : (P : Subgroup G) ≤ MulAction.stabilizer G x := by
    intro g hg
    exact hx ⟨g, hg⟩
  have hi : ¬2 ∣ (MulAction.stabilizer G x).index :=
    fun h => P.not_dvd_index (h.trans (Subgroup.index_dvd_of_le hP))
  let O := MulAction.orbit G x
  let : Fintype O := (Finite.finite_mulAction_orbit (M := G) x).fintype
  have hcard : ¬2 ∣ Fintype.card O := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr (MulAction.orbitEquivQuotientStabilizer G x)]
    exact hi
  let y : V := ∑ v : O, (v : V)
  have hy : y ∈ Representation.invariants ρ := by
    intro g
    change ρ g (∑ v : O, (v : V)) = ∑ v : O, (v : V)
    rw [map_sum]
    exact Fintype.sum_equiv (MulAction.toPerm g : Equiv.Perm O)
      (fun v : O => ρ g (v : V)) (fun v : O => (v : V)) (fun _ => rfl)
  have hy0 : f y = 0 := hfix hy
  have hyf : f y = (Fintype.card O : ZMod 2) * f x := by
    change f (∑ v : O, (v : V)) = _
    rw [map_sum]
    have he (v : O) : f (v : V) = f x := by
      obtain ⟨g, hg⟩ := v.property
      exact (congrArg f hg).symm.trans (hf g x)
    simp only [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : (Fintype.card O : ZMod 2) ≠ 0 := by
    exact fun h => hcard ((ZMod.natCast_eq_zero_iff _ _).mp h)
  exact (mul_eq_zero.mp (hyf.symm.trans hy0)).resolve_left hc

end Representation.BinaryOffender
