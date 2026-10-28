module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.Pair00
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.Pair01
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.Pair10
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.Pair11
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Plane
import Mathlib.Tactic.FinCases

/-!
# Actual planes at the four literal Held pairs

The two published generators commute, have cube one, and their nine coordinate
products act distinctly at a certified permutation point. Their power-product
homomorphism therefore identifies its range, the literal candidateOdd, with
F₃². This is an explicit multiplicative equivalence, with no ambient order,
realization, normalizer-bound, or subgroup-catalogue assumption.

The chosen axes are the original generators except for (true,0), where they
are r₁ and r₀r₁. The formulas for this basis change are proved here; identifying
the actual inner action image with the diagonal group remains a separate
calculation, and is not claimed merely by this choice of coordinates.

Sources: the original ATLAS HeG1-p2058B0 permutations and the max3/max4 words
retained with Candidates; GLS3 Table 5.3p; Aschbacher–Smith, printed pp.509–511.
The finite certificates live in Pair00/01/10/11 and use kernel reduction.
-/

@[expose] public section
namespace Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages
open Subgroup

theorem oddGenerator_cube (i : Bool) (j k : Fin 2) : oddGenerator i j k ^ 3 = 1 := by
  cases i <;> fin_cases j <;> fin_cases k
  · exact Pair00.odd0_cube
  · exact Pair00.odd1_cube
  · exact Pair01.odd0_cube
  · exact Pair01.odd1_cube
  · exact Pair10.odd0_cube
  · exact Pair10.odd1_cube
  · exact Pair11.odd0_cube
  · exact Pair11.odd1_cube

theorem oddGenerator_commute (i : Bool) (j : Fin 2) :
    Commute (oddGenerator i j 0) (oddGenerator i j 1) := by
  cases i <;> fin_cases j
  · exact Pair00.odd_commute
  · exact Pair01.odd_commute
  · exact Pair10.odd_commute
  · exact Pair11.odd_commute

/-- Products in the published generating pair. -/
def oddEmbedding (i : Bool) (j : Fin 2) : Plane →* He where
  toFun v := oddGenerator i j 0 ^ (v.toAdd 0).val * oddGenerator i j 1 ^ (v.toAdd 1).val
  map_one' := by simp
  map_mul' u v := by
    change _ ^ (u.toAdd 0 + v.toAdd 0).val * _ ^ (u.toAdd 1 + v.toAdd 1).val = _
    rw [ZMod.val_add, ZMod.val_add,
      ← pow_eq_pow_mod _ (oddGenerator_cube i j 0),
      ← pow_eq_pow_mod _ (oddGenerator_cube i j 1), pow_add, pow_add]
    exact ((oddGenerator_commute i j).symm.pow_pow (u.toAdd 1).val (v.toAdd 0).val).mul_mul_mul_comm _ _ |>.symm

theorem oddEmbedding_apply (i : Bool) (j : Fin 2) (v : Plane) :
    oddEmbedding i j v =
      oddGenerator i j 0 ^ (v.toAdd 0).val * oddGenerator i j 1 ^ (v.toAdd 1).val := rfl

/-- The two standard coordinate vectors in multiplicative notation. -/
def coordinateVector (k : Fin 2) : Plane :=
  Multiplicative.ofAdd (fun l => if l = k then 1 else 0)

theorem oddEmbedding_vector (i : Bool) (j k : Fin 2) :
    oddEmbedding i j (coordinateVector k) = oddGenerator i j k := by
  fin_cases k <;> simp [oddEmbedding_apply, coordinateVector, ZMod.val_one]

theorem oddEmbedding_range (i : Bool) (j : Fin 2) :
    (oddEmbedding i j).range = candidateOdd i j := by
  apply le_antisymm
  · rintro g ⟨v, rfl⟩
    exact (candidateOdd i j).mul_mem
      ((candidateOdd i j).pow_mem (oddGenerator_mem i j 0) _)
      ((candidateOdd i j).pow_mem (oddGenerator_mem i j 1) _)
  · apply (closure_le _).mpr
    rintro g ⟨k, rfl⟩
    exact ⟨coordinateVector k, oddEmbedding_vector i j k⟩

private def separationPoint : Bool → Fin 2 → Fin 2058
  | false, 0 => Pair00.separationPoint
  | false, 1 => Pair01.separationPoint
  | true, 0 => Pair10.separationPoint
  | true, 1 => Pair11.separationPoint

private theorem coordinates_separate (i : Bool) (j : Fin 2) (u v : ZMod 3)
    (h : representation (oddGenerator i j 0 ^ u.val * oddGenerator i j 1 ^ v.val) (separationPoint i j) = separationPoint i j) :
    u = 0 ∧ v = 0 := by
  simp only [map_mul, map_pow] at h
  cases i <;> fin_cases j
  · apply Pair00.coordinates_separate u v
    rw [Pair00.odd0_eq, Pair00.odd1_eq]
    convert h using 1 <;> rfl
  · apply Pair01.coordinates_separate u v
    rw [Pair01.odd0_eq, Pair01.odd1_eq]
    convert h using 1 <;> rfl
  · apply Pair10.coordinates_separate u v
    rw [Pair10.odd0_eq, Pair10.odd1_eq]
    convert h using 1 <;> rfl
  · apply Pair11.coordinates_separate u v
    rw [Pair11.odd0_eq, Pair11.odd1_eq]
    convert h using 1 <;> rfl

theorem oddEmbedding_injective (i : Bool) (j : Fin 2) : Function.Injective (oddEmbedding i j) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro v hv
  have h := congrArg (fun g : He => representation g (separationPoint i j)) hv
  have hc := coordinates_separate i j (v.toAdd 0) (v.toAdd 1) h
  funext k
  fin_cases k
  · exact hc.1
  · exact hc.2

/-- Actual coordinates in the two original generators. -/
noncomputable def rawEquiv (i : Bool) (j : Fin 2) : candidateOdd i j ≃* Plane :=
  ((MonoidHom.ofInjective (oddEmbedding_injective i j)).trans
    (MulEquiv.subgroupCongr (oddEmbedding_range i j))).symm

theorem rawEquiv_symm_apply (i : Bool) (j : Fin 2) (v : Plane) :
    (rawEquiv i j).symm v = ⟨oddEmbedding i j v, (oddEmbedding_range i j) ▸ ⟨v, rfl⟩⟩ := rfl

/-- Columns (0,1) and (1,1): the diagonal axes for representative (true,0). -/
def exceptionalBasis : MulAut Plane := AddEquiv.toMultiplicative {
  toFun := fun x => ![x 1, x 0 + x 1]
  invFun := fun x => ![x 1 - x 0, x 0]
  left_inv := by intro x; funext k; fin_cases k <;> simp
  right_inv := by intro x; funext k; fin_cases k <;> simp
  map_add' := by intro x y; funext k; fin_cases k <;> simp [add_assoc, add_left_comm, add_comm] }

/-- The basis in which the representative action calculations are to be made. -/
def basisChange (i : Bool) (j : Fin 2) : MulAut Plane :=
  if i = true ∧ j = 0 then exceptionalBasis else 1

/-- Genuine plane coordinates, without realization or normalizer assumptions. -/
noncomputable def candidateOddEquiv (i : Bool) (j : Fin 2) : candidateOdd i j ≃* Plane :=
  (rawEquiv i j).trans (basisChange i j).symm

/-- The actual marked axes used by the action calculations. -/
def basisGenerator (i : Bool) (j k : Fin 2) : He :=
  if i = true ∧ j = 0 then
    if k = 0 then oddGenerator i j 1 else oddGenerator i j 0 * oddGenerator i j 1
  else oddGenerator i j k

theorem basisGenerator_mem (i : Bool) (j k : Fin 2) :
    basisGenerator i j k ∈ candidateOdd i j := by
  unfold basisGenerator
  split
  · split
    · exact oddGenerator_mem i j 1
    · exact (candidateOdd i j).mul_mem (oddGenerator_mem i j 0) (oddGenerator_mem i j 1)
  · exact oddGenerator_mem i j k

theorem candidateOddEquiv_symm_vector (i : Bool) (j k : Fin 2) :
    ((candidateOddEquiv i j).symm (coordinateVector k) : He) = basisGenerator i j k := by
  change oddEmbedding i j (basisChange i j (coordinateVector k)) = _
  cases i <;> fin_cases j <;> fin_cases k <;>
    simp [basisChange, basisGenerator, exceptionalBasis, coordinateVector, oddEmbedding_apply, ZMod.val_one]

theorem candidateOddEquiv_basisGenerator (i : Bool) (j k : Fin 2) :
    candidateOddEquiv i j ⟨basisGenerator i j k, basisGenerator_mem i j k⟩ = coordinateVector k := by
  apply (candidateOddEquiv i j).symm.injective
  apply Subtype.ext
  simpa only [MulEquiv.symm_apply_apply] using (candidateOddEquiv_symm_vector i j k).symm

theorem candidateOdd_card (i : Bool) (j : Fin 2) : Nat.card (candidateOdd i j) = 9 := by
  rw [Nat.card_congr (candidateOddEquiv i j).toEquiv, Nat.card_eq_fintype_card]
  decide +kernel

end Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages
