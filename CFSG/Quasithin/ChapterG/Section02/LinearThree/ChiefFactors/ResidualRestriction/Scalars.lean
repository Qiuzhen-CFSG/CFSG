module
public import Theory.SpecificGroups.PSL3.LinearThreeFlags
public import Theory.GroupTheory.PResidual.FiniteImage
public import Mathlib.FieldTheory.Finite.Basic
/-!
# Odd scalars survive the two-residual of a point parabolic

The diagonal homomorphism a ↦ diag(a,a⁻¹,1) has image in the full point
parabolic. Every odd-order unit therefore supplies an element of its
O² residual. Its action on the marked point is multiplication by a.
For a field of order four this produces a cube-one element moving e₀.
Thus the point cannot be declared central by invoking the solvable-residual
calculation. This is an obstruction to that local interface, not a
counterexample to all the ambient hypotheses of G.2.5.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Hypothesis G.2.1 and G.2.5(8), printed pp.332,335–336.
-/

@[expose] public section
open Subgroup Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction
open Matrix.PSL3.LinearThree
variable (F : Type*) [Field F] [Finite F]

def pointTorusHom : Fˣ →* pointParabolicSL F where
  toFun a := ⟨pointTorus F a, (pointTorus_mem_borel F a).1⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pointTorus]
  map_mul' a b := by
    apply Subtype.ext
    apply Subtype.ext
    change diagonal _ = diagonal _ * diagonal _
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp [mul_comm]

theorem pointTorus_mem_twoResidual (a : Fˣ) (ha : Nat.Coprime 2 (orderOf a)) :
    pointTorus F a ∈ (pResidual 2 (pointParabolicSL F)).map (pointParabolicSL F).subtype := by
  exact ⟨pointTorusHom F a, mem_pResidual_of_orderOf_coprime
    (ha.of_dvd_right (orderOf_map_dvd (pointTorusHom F) a)), rfl⟩

omit [Finite F] in
theorem pointTorus_action (a : Fˣ) :
    (pointTorus F a).val *ᵥ (![1, 0, 0] : Fin 3 → F) = ![(a : F), 0, 0] := by
  ext i
  fin_cases i <;> simp [pointTorus, mulVec, dotProduct, Fin.sum_univ_three]

theorem odd_unit_moves_point (a : Fˣ) (ha : Nat.Coprime 2 (orderOf a)) (hne : a ≠ 1) :
    ∃ x ∈ (pResidual 2 (pointParabolicSL F)).map (pointParabolicSL F).subtype,
      x.val *ᵥ (![1, 0, 0] : Fin 3 → F) ≠ ![1, 0, 0] := by
  refine ⟨pointTorus F a, pointTorus_mem_twoResidual F a ha, ?_⟩
  rw [pointTorus_action]
  intro he
  apply hne
  apply Units.ext
  exact congrFun he 0

theorem four_element_scalar_obstruction (hF : Nat.card F = 4) :
    ∃ x ∈ (pResidual 2 (pointParabolicSL F)).map (pointParabolicSL F).subtype,
      x ^ 3 = 1 ∧ x.val *ᵥ (![1, 0, 0] : Fin 3 → F) ≠ ![1, 0, 0] := by
  have hc : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF]
  have hn : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp (by rw [hc]; decide)
  obtain ⟨a, ha⟩ := exists_ne (1 : Fˣ)
  have hcop : Nat.Coprime 2 (orderOf a) :=
    Nat.Coprime.of_dvd_right (_root_.orderOf_dvd_natCard a) (by rw [hc]; decide)
  refine ⟨pointTorus F a, pointTorus_mem_twoResidual F a hcop, ?_, ?_⟩
  · have hp : a ^ 3 = 1 := by simpa only [hc] using pow_card_eq_one' (x := a)
    have he := congrArg (pointParabolicSL F).subtype
      (show pointTorusHom F a ^ 3 = 1 by rw [← map_pow, hp, map_one])
    exact he
  · rw [pointTorus_action]
    intro he
    exact ha (Units.ext (congrFun he 0))
end CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction
