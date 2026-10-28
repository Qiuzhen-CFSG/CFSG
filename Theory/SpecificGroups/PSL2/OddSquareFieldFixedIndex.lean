module

public import Theory.SpecificGroups.PSL2.OddSquareFieldFixed
public import Theory.SpecificGroups.SL2.OddOrderDivisibility
public import GorensteinWalter.PSL2PerfectOfCard
public import GorensteinWalter.PGL2Cardinality
public import Theory.FieldTheory.FiniteAutomorphismOrder
import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
/-!
# Odd-index nonsolvable fixed subgroup

For a nontrivial coefficient involution of an odd quadratic field, the
fixed PSL₂ subgroup is PGL₂ over the fixed prime field. Its index is odd, it
is proper, and it is nonsolvable. This is the concrete prime-subfield
obstruction used against inner-field automizers in E.2.2(2c).
-/

public section
open Subgroup GorensteinWalter
open scoped MatrixGroups
namespace Theory.PSL2.OddSquareFieldFixed
/-- The coefficient-fixed subgroup has odd index and remains nonsolvable. -/
theorem coefficient_fixed_odd_index_nonsolvable
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hp : 3 < p) (hF : Nat.card F = p ^ 2)
    (σ : F ≃+* F) (hσ : orderOf σ = 2) :
    Odd (psl2FieldAut F σ).fixedSubgroup.index ∧
      (psl2FieldAut F σ).fixedSubgroup ≠ ⊤ ∧
      ¬ Group.IsSolvable (psl2FieldAut F σ).fixedSubgroup := by
  let E := FixedPoints.subfield (zpowers σ) F
  let P := (psl2FieldAut F σ).fixedSubgroup
  have hE : Nat.card E = p := fixed_subfield_card hF σ hσ
  obtain ⟨d⟩ := coefficient_fixed_equiv ho hF σ hσ
  have hP : Nat.card P = p * (p ^ 2 - 1) := by
    rw [Nat.card_congr d.toEquiv, pgl2_card_formula, hE]
  have hG := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice (F := F) (hF ▸ ho.pow)
  rw [hF] at hG
  have hidx := P.card_mul_index
  have hp2 : 1 ≤ p ^ 2 := by nlinarith
  have hsub : p ^ 2 - 1 + 1 = p ^ 2 := Nat.sub_add_cancel hp2
  have hsub4 : (p ^ 2) ^ 2 - 1 + 1 = (p ^ 2) ^ 2 := Nat.sub_add_cancel (by nlinarith)
  have hfactor : p ^ 2 * ((p ^ 2) ^ 2 - 1) = (p * (p ^ 2 - 1)) * (p * (p ^ 2 + 1)) := by
    zify [hp2] at hsub hsub4 ⊢
    nlinarith only [hsub, hsub4]
  have hi : 2 * P.index = p * (p ^ 2 + 1) := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := P))
    calc
      Nat.card P * (2 * P.index) = (Nat.card P * P.index) * 2 := by ring
      _ = p ^ 2 * ((p ^ 2) ^ 2 - 1) := by rw [hidx]; exact hG
      _ = Nat.card P * (p * (p ^ 2 + 1)) := by rw [hP]; exact hfactor
  have hiodd : Odd P.index := by
    have hm := congrArg (fun n : ℕ => n % 4) hi
    have hodd := Nat.odd_iff.mp ho
    have hb := Nat.mod_lt p (by decide : 0 < 4)
    have hpmod : p % 4 = 1 ∨ p % 4 = 3 := by omega
    have hr : (p * (p ^ 2 + 1)) % 4 = 2 := by
      rw [Nat.mul_mod, Nat.add_mod, Nat.pow_mod]
      rcases hpmod with hh | hh <;> norm_num [hh]
    rw [hr] at hm
    exact Nat.odd_iff.mpr (by omega)
  have hPne : P ≠ ⊤ := by
    intro he
    have hindex : P.index = 1 := index_eq_one.mpr he
    rw [hindex] at hi
    nlinarith
  refine ⟨hiodd, hPne, ?_⟩
  intro hs
  let := hs
  let : Group.IsSolvable (PGL2 E) := Group.isSolvable_of_surjective (f := d.toMonoidHom) d.surjective
  let : Group.IsPerfect (PSL2 E) := psl2_isPerfect_of_card_gt_three E (by omega)
  let : IsSimpleGroup (PSL2 E) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  exact Group.IsPerfect.not_isSolvable (PSL2 E)
    (Group.isSolvable_of_isSolvable_injective
      (f := Matrix.ProjectiveSpecialLinearGroup.toPGL)
      Matrix.ProjectiveSpecialLinearGroup.toPGL_injective)
end Theory.PSL2.OddSquareFieldFixed
