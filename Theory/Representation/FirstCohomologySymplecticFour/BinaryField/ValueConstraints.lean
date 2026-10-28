module

public import Theory.Representation.FirstCohomologySymplecticFour.BinaryField.Generators
public import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# Binary cocycle values on three derived symplectic generators

Three matrix relations impose seven linear constraints on the twelve coordinates
of a cocycle on the selected commutators. The remaining five coordinates determine
one scalar and a principal vector. Thus every cocycle agrees on these commutators
with a scalar multiple of the quadratic-defect cocycle plus a principal cocycle.
No assertion that the commutators generate the group is needed here.

The relations are checked by kernel reduction of their explicit binary matrices.
The quadratic values follow from the row-defect square formula and injectivity
of squaring; all subsequent coordinate calculations are linear algebra over F₂.

Reference: Aschbacher--Smith, *The Classification of Quasithin Groups*,
Lemma I.1.6(5), printed p.408 (PDF p.419).
-/

public section

open Matrix

namespace Representation.OneCohomology.SymplecticFour.BinaryField
local notation "V" => (Fin 2 ⊕ Fin 2) → ZMod 2
local notation "a" => (Sum.inl (0 : Fin 2) : Fin 2 ⊕ Fin 2)
local notation "b" => (Sum.inl (1 : Fin 2) : Fin 2 ⊕ Fin 2)
local notation "c" => (Sum.inr (0 : Fin 2) : Fin 2 ⊕ Fin 2)
local notation "d" => (Sum.inr (1 : Fin 2) : Fin 2 ⊕ Fin 2)

private lemma generator_commute : generator 1 * generator 0 = generator 0 * generator 1 := by
  apply Subtype.ext
  apply Subtype.ext
  change (generator 1).val.val * (generator 0).val.val =
    (generator 0).val.val * (generator 1).val.val
  simp only [generator_val]
  decide

private lemma generator_square_relation : generator 2 * (generator 0 * generator 0) =
    generator 0 * (generator 2 * generator 2) := by
  apply Subtype.ext
  apply Subtype.ext
  change (generator 2).val.val * ((generator 0).val.val * (generator 0).val.val) =
    (generator 0).val.val * ((generator 2).val.val * (generator 2).val.val)
  simp only [generator_val]
  decide

private lemma generator_braid_relation : generator 2 * (generator 0 * generator 2) =
    generator 0 * (generator 2 * generator 0) := by
  apply Subtype.ext
  apply Subtype.ext
  change (generator 2).val.val * ((generator 0).val.val * (generator 2).val.val) =
    (generator 0).val.val * ((generator 2).val.val * (generator 0).val.val)
  simp only [generator_val]
  decide

private lemma cocycle_mul (f : cocycles (symplecticDerivedNatural (k := ZMod 2) 2))
    (g h : commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))) :
    f.val (g * h) = g.val.val *ᵥ f.val h + f.val g := f.property g h

private lemma cocycle_commute (f : cocycles (symplecticDerivedNatural (k := ZMod 2) 2)) :
    generatorMatrix 1 *ᵥ f.val (generator 0) + f.val (generator 1) =
      generatorMatrix 0 *ᵥ f.val (generator 1) + f.val (generator 0) := by
  have h := congrArg f.val generator_commute
  simpa only [cocycle_mul, generator_val] using h

private lemma cocycle_square_relation (f : cocycles (symplecticDerivedNatural (k := ZMod 2) 2)) :
    generatorMatrix 2 *ᵥ (generatorMatrix 0 *ᵥ f.val (generator 0) + f.val (generator 0)) + f.val (generator 2) =
      generatorMatrix 0 *ᵥ (generatorMatrix 2 *ᵥ f.val (generator 2) + f.val (generator 2)) + f.val (generator 0) := by
  have h := congrArg f.val generator_square_relation
  simpa only [cocycle_mul, generator_val] using h

private lemma cocycle_braid_relation (f : cocycles (symplecticDerivedNatural (k := ZMod 2) 2)) :
    generatorMatrix 2 *ᵥ (generatorMatrix 0 *ᵥ f.val (generator 2) + f.val (generator 0)) + f.val (generator 2) =
      generatorMatrix 0 *ᵥ (generatorMatrix 2 *ᵥ f.val (generator 0) + f.val (generator 2)) + f.val (generator 0) := by
  have h := congrArg f.val generator_braid_relation
  simpa only [cocycle_mul, generator_val] using h

private lemma constraints (f : cocycles (symplecticDerivedNatural (k := ZMod 2) 2)) :
    f.val (generator 0) a = 0 ∧ f.val (generator 0) c = 0 ∧
    f.val (generator 1) b = 0 ∧ f.val (generator 1) d = 0 ∧
    f.val (generator 2) a = 0 ∧ f.val (generator 2) b = f.val (generator 2) c ∧
    f.val (generator 2) d = f.val (generator 0) d := by
  have ha := congrFun (cocycle_commute f) a
  have hb := congrFun (cocycle_commute f) b
  have hc := congrFun (cocycle_commute f) c
  have hd := congrFun (cocycle_commute f) d
  have h₂a := congrFun (cocycle_square_relation f) a
  have h₂c := congrFun (cocycle_square_relation f) c
  have h₃c := congrFun (cocycle_braid_relation f) c
  simp [generatorMatrix, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Fin.sum_univ_two, CharTwo.add_self_eq_zero] at ha hb hc hd h₂a h₂c h₃c
  have h0a : f.val (generator 0) a = 0 := by linear_combination hc
  have h0c : f.val (generator 0) c = 0 := by linear_combination ha + hc
  have h1b : f.val (generator 1) b = 0 := by linear_combination -hd
  have h1d : f.val (generator 1) d = 0 := by linear_combination -hb - hd
  have h2a : f.val (generator 2) a = 0 := h₂a.trans h0a
  have h2bc : f.val (generator 2) b = f.val (generator 2) c := by
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) h₃c - h2a + h0c
  have h2d : f.val (generator 2) d = f.val (generator 0) d := by
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) -h₂c - h2a - h2bc - h0c
  exact ⟨h0a, h0c, h1b, h1d, h2a, h2bc, h2d⟩

private def quadraticValues (j : Fin 3) : V :=
  ![Sum.elim ![0, 0] ![0, 1], Sum.elim ![0, 0] ![1, 0],
    Sum.elim ![0, 0] ![0, 1]] j

private lemma quadraticValues_eq (j : Fin 3) :
    (derivedQuadraticCocycle (K := ZMod 2)).val (generator j) = quadraticValues j := by
  funext i
  apply CharTwo.sq_injective (R := ZMod 2)
  dsimp only
  rw [derivedQuadraticCocycle_apply_sq, generator_val]
  have h : ∀ j i, rowQuadratic (generatorMatrix j i) = (quadraticValues j i) ^ 2 := by decide
  exact h j i

/-- Every binary cocycle agrees on the three selected commutators with a scalar
multiple of the quadratic-defect cocycle plus a principal cocycle. -/
theorem exists_generator_values (f : cocycles (symplecticDerivedNatural (k := ZMod 2) 2)) :
    ∃ (t : ZMod 2) (v : V), ∀ j : Fin 3,
      f.val (generator j) =
        (t • derivedQuadraticCocycle + principal (symplecticDerivedNatural 2) v).val (generator j) := by
  obtain ⟨h0a, h0c, h1b, h1d, h2a, h2bc, h2d⟩ := constraints f
  let t := f.val (generator 1) c + f.val (generator 2) b + f.val (generator 0) b
  let va := f.val (generator 2) b + f.val (generator 0) b
  let vb := f.val (generator 0) d + t
  let v : V := Sum.elim ![va, vb] ![f.val (generator 1) a + va, f.val (generator 0) b + vb]
  refine ⟨t, v, ?_⟩
  intro j
  funext i
  change f.val (generator j) i = t * (derivedQuadraticCocycle (K := ZMod 2)).val (generator j) i +
    (((generator j).val.val *ᵥ v) i - v i)
  rw [quadraticValues_eq, generator_val]
  fin_cases j <;> rcases i with i | i <;> fin_cases i <;>
    simp [v, va, vb, t, quadraticValues, generatorMatrix, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type, Fin.sum_univ_two, h0a, h0c, h1b, h1d, h2a, h2bc, h2d] <;>
    ring_nf <;> simp [CharTwo.two_eq_zero, show (3 : ZMod 2) = 1 by decide,
      show (4 : ZMod 2) = 0 by decide]

end Representation.OneCohomology.SymplecticFour.BinaryField
