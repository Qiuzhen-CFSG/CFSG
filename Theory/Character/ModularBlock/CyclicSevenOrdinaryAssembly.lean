module

public import Theory.Character.ModularBlock.CyclicSevenIntegralData
public import Theory.Character.CyclicSevenColumnArithmetic

/-!
# Assembly of the ordinary order-seven rows

Integral restriction multiplicities and the two column equations suffice to
construct the five ordinary rows. Period irrationality first excludes the
principal character from the three exceptional rows. The integer column lemma
then removes their common shift and enumerates the two constant sign rows,
placing the principal character first. Every remaining row has value zero on
all nonidentity elements of the subgroup.

The character-theoretic construction of the inputs is separate: this module
proves the assembly for explicit `IntegralValues` and `ColumnEquations`.
Source: Fong (1967), printed p.75, citing Brauer (1942).
Adapted from `Theory.Character.ModularBlock.CyclicThirteenOrdinaryAssembly`,
whose source is Alperin--Brauer--Gorenstein, III.8, pp.116--117.
-/

public section
noncomputable section
open scoped BigOperators
namespace ModularBlock.CyclicSeven
open PrimeBlockConstruction PrincipalBlockConstruction CyclicSevenNormalizer
variable {G : Type*} [Group G] [Finite G]
variable {d : PrimeCongruenceBlockData 7 G} {P : Sylow 7 G}
  {s : PeriodRows (P : Subgroup G)}

/-- A shifted signed quadratic period cannot be the value of the principal character. -/
theorem IntegralValues.principal_not_exceptional (v : IntegralValues d P s) :
    d.principal ∉ Set.range v.exceptionalRows := by
  rintro ⟨k,hk⟩
  have hv := v.exceptional_value k s.generator s.generator_ne_one
  rw [hk, d.principal_eq, ordinaryPrincipalCharacter_apply, s.period_value] at hv
  apply SevenPeriods.period_not_rational s.root_primitive s.periods k
  rcases v.sign_unit with h | h
  · refine ⟨((1 - v.shift : ℤ) : ℚ), ?_⟩
    push_cast
    rw [h] at hv
    norm_num at hv
    linear_combination -hv
  · refine ⟨((v.shift - 1 : ℤ) : ℚ), ?_⟩
    push_cast
    rw [h] at hv
    norm_num at hv
    linear_combination hv

/-- Assemble all five actual ordinary rows from integral restrictions and
ordinary column orthogonality. -/
theorem IntegralValues.ordinaryRows (v : IntegralValues d P s) (q : ColumnEquations v) :
    Nonempty (OrdinaryRows d P) := by
  classical
  let R := {i : d.I // i ∉ Set.range v.exceptionalRows}
  let p : R := ⟨d.principal, v.principal_not_exceptional⟩
  have hp : v.remainder p = 1 := by
    have hh := v.remainder_value p s.generator s.generator_ne_one
    change d.chi d.principal _ = _ at hh
    rw [d.principal_eq, ordinaryPrincipalCharacter_apply] at hh
    exact_mod_cast hh.symm
  have hnp : (q.degree p : ℤ) = 1 := by
    have hh := q.degree_value p
    change d.chi d.principal _ = _ at hh
    rw [d.principal_eq, ordinaryPrincipalCharacter_apply] at hh
    exact_mod_cast hh.symm
  obtain ⟨hc,hs⟩ := CyclicSevenColumnArithmetic.shift_eq_zero
    v.remainder (fun i => (q.degree i : ℤ)) p hp hnp
    v.shift v.sign (v.commonDegree : ℤ) v.sign_unit
    (by exact_mod_cast v.degree_pos) q.column q.degree_sum
  obtain ⟨e, he, hsign, hzero⟩ :=
    CyclicSevenColumnArithmetic.exists_two_sign_rows v.remainder p hp hs
  let f : Fin 5 → d.I := fun i => Fin.addCases (fun j => (e j).val) (fun k => v.exceptionalRows k) i
  have hfinj : Function.Injective f := by
    intro i j hij
    induction i using Fin.addCases (m := 2) (n := 3) with
    | left i =>
      induction j using Fin.addCases (m := 2) (n := 3) with
      | left j =>
        simp only [f, Fin.addCases_left] at hij
        exact congrArg (Fin.castAdd 3) (e.injective (Subtype.ext hij))
      | right j =>
        simp only [f, Fin.addCases_left, Fin.addCases_right] at hij
        exact False.elim ((e i).property ⟨j,hij.symm⟩)
    | right i =>
      induction j using Fin.addCases (m := 2) (n := 3) with
      | left j =>
        simp only [f, Fin.addCases_left, Fin.addCases_right] at hij
        exact False.elim ((e j).property ⟨i,hij⟩)
      | right j =>
        simp only [f, Fin.addCases_right] at hij
        exact congrArg (Fin.natAdd 2) (v.exceptionalRows.injective hij)
  let rows : Fin 5 ↪ d.I := ⟨f,hfinj⟩
  refine ⟨{
    rows := rows
    principal_row := ?_
    sign := fun j => v.remainder (e j)
    sign_unit := hsign
    sign_zero := by rw [he, hp]
    nonexceptional_value := ?_
    exceptionalDegree := v.commonDegree
    exceptional_degree := ?_
    exceptionalSign := -v.sign
    exceptionalSign_unit := ?_
    generator := s.generator
    generator_ne_one := s.generator_ne_one
    root := s.root
    root_primitive := s.root_primitive
    periods := s.periods
    exceptional_value := ?_
    off_rows_vanish := ?_ }⟩
  · change (e 0).val = d.principal
    exact congrArg Subtype.val he
  · intro j u hu
    simpa [rows, f] using v.remainder_value (e j) u hu
  · intro k
    simpa [rows, f] using v.degree k
  · rcases v.sign_unit with h | h <;> simp [h]
  · intro k
    simpa [rows, f, hc, s.period_value] using
      v.exceptional_value k s.generator s.generator_ne_one
  · intro i hi u hu
    have hi' : i ∉ Set.range v.exceptionalRows := by
      rintro ⟨k,rfl⟩
      exact hi ⟨k.natAdd 2, by simp [rows, f]⟩
    let r : R := ⟨i,hi'⟩
    have hr : r ∉ Set.range e := by
      rintro ⟨j,hj⟩
      apply hi
      refine ⟨j.castAdd 3, ?_⟩
      change f (j.castAdd 3) = i
      simpa [f] using congrArg Subtype.val hj
    simpa [hzero r hr] using v.remainder_value r u hu
end ModularBlock.CyclicSeven
