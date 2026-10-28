module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Alternating.Curry
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.Group.Subgroup.Defs

/-!
# A binary alternating quartic and its intrinsic rank statistic

The coefficient word below uses increasing quadruples in lexicographic order.
The form is a sum of four-coordinate determinants, so alternation and
multilinearity hold independently of any finite computation. Contraction rank
is the dimension of the image in the dual space. Its distribution is invariant
under every linear equivalence preserving the form.

The literal coefficients and point marking originate in the reproducible
operator-algebra calculation documented in
`Scratch/J4FleetGuidance/SeedCentralizer/README.md` in the source repository.
No output of that calculation is taken as a proof of a rank or orbit assertion.
-/

@[expose] public section

namespace BinaryQuarticMathieu

abbrev F := ZMod 2
abbrev U := Fin 10 → F
abbrev Form := U [⋀^Fin 4]→ₗ[F] F

/-- Lexicographic increasing quadruples of coordinate indices. -/
def quadrupleArray : Array (Fin 4 → Fin 10) := #[
  ![0, 1, 2, 3],
  ![0, 1, 2, 4],
  ![0, 1, 2, 5],
  ![0, 1, 2, 6],
  ![0, 1, 2, 7],
  ![0, 1, 2, 8],
  ![0, 1, 2, 9],
  ![0, 1, 3, 4],
  ![0, 1, 3, 5],
  ![0, 1, 3, 6],
  ![0, 1, 3, 7],
  ![0, 1, 3, 8],
  ![0, 1, 3, 9],
  ![0, 1, 4, 5],
  ![0, 1, 4, 6],
  ![0, 1, 4, 7],
  ![0, 1, 4, 8],
  ![0, 1, 4, 9],
  ![0, 1, 5, 6],
  ![0, 1, 5, 7],
  ![0, 1, 5, 8],
  ![0, 1, 5, 9],
  ![0, 1, 6, 7],
  ![0, 1, 6, 8],
  ![0, 1, 6, 9],
  ![0, 1, 7, 8],
  ![0, 1, 7, 9],
  ![0, 1, 8, 9],
  ![0, 2, 3, 4],
  ![0, 2, 3, 5],
  ![0, 2, 3, 6],
  ![0, 2, 3, 7],
  ![0, 2, 3, 8],
  ![0, 2, 3, 9],
  ![0, 2, 4, 5],
  ![0, 2, 4, 6],
  ![0, 2, 4, 7],
  ![0, 2, 4, 8],
  ![0, 2, 4, 9],
  ![0, 2, 5, 6],
  ![0, 2, 5, 7],
  ![0, 2, 5, 8],
  ![0, 2, 5, 9],
  ![0, 2, 6, 7],
  ![0, 2, 6, 8],
  ![0, 2, 6, 9],
  ![0, 2, 7, 8],
  ![0, 2, 7, 9],
  ![0, 2, 8, 9],
  ![0, 3, 4, 5],
  ![0, 3, 4, 6],
  ![0, 3, 4, 7],
  ![0, 3, 4, 8],
  ![0, 3, 4, 9],
  ![0, 3, 5, 6],
  ![0, 3, 5, 7],
  ![0, 3, 5, 8],
  ![0, 3, 5, 9],
  ![0, 3, 6, 7],
  ![0, 3, 6, 8],
  ![0, 3, 6, 9],
  ![0, 3, 7, 8],
  ![0, 3, 7, 9],
  ![0, 3, 8, 9],
  ![0, 4, 5, 6],
  ![0, 4, 5, 7],
  ![0, 4, 5, 8],
  ![0, 4, 5, 9],
  ![0, 4, 6, 7],
  ![0, 4, 6, 8],
  ![0, 4, 6, 9],
  ![0, 4, 7, 8],
  ![0, 4, 7, 9],
  ![0, 4, 8, 9],
  ![0, 5, 6, 7],
  ![0, 5, 6, 8],
  ![0, 5, 6, 9],
  ![0, 5, 7, 8],
  ![0, 5, 7, 9],
  ![0, 5, 8, 9],
  ![0, 6, 7, 8],
  ![0, 6, 7, 9],
  ![0, 6, 8, 9],
  ![0, 7, 8, 9],
  ![1, 2, 3, 4],
  ![1, 2, 3, 5],
  ![1, 2, 3, 6],
  ![1, 2, 3, 7],
  ![1, 2, 3, 8],
  ![1, 2, 3, 9],
  ![1, 2, 4, 5],
  ![1, 2, 4, 6],
  ![1, 2, 4, 7],
  ![1, 2, 4, 8],
  ![1, 2, 4, 9],
  ![1, 2, 5, 6],
  ![1, 2, 5, 7],
  ![1, 2, 5, 8],
  ![1, 2, 5, 9],
  ![1, 2, 6, 7],
  ![1, 2, 6, 8],
  ![1, 2, 6, 9],
  ![1, 2, 7, 8],
  ![1, 2, 7, 9],
  ![1, 2, 8, 9],
  ![1, 3, 4, 5],
  ![1, 3, 4, 6],
  ![1, 3, 4, 7],
  ![1, 3, 4, 8],
  ![1, 3, 4, 9],
  ![1, 3, 5, 6],
  ![1, 3, 5, 7],
  ![1, 3, 5, 8],
  ![1, 3, 5, 9],
  ![1, 3, 6, 7],
  ![1, 3, 6, 8],
  ![1, 3, 6, 9],
  ![1, 3, 7, 8],
  ![1, 3, 7, 9],
  ![1, 3, 8, 9],
  ![1, 4, 5, 6],
  ![1, 4, 5, 7],
  ![1, 4, 5, 8],
  ![1, 4, 5, 9],
  ![1, 4, 6, 7],
  ![1, 4, 6, 8],
  ![1, 4, 6, 9],
  ![1, 4, 7, 8],
  ![1, 4, 7, 9],
  ![1, 4, 8, 9],
  ![1, 5, 6, 7],
  ![1, 5, 6, 8],
  ![1, 5, 6, 9],
  ![1, 5, 7, 8],
  ![1, 5, 7, 9],
  ![1, 5, 8, 9],
  ![1, 6, 7, 8],
  ![1, 6, 7, 9],
  ![1, 6, 8, 9],
  ![1, 7, 8, 9],
  ![2, 3, 4, 5],
  ![2, 3, 4, 6],
  ![2, 3, 4, 7],
  ![2, 3, 4, 8],
  ![2, 3, 4, 9],
  ![2, 3, 5, 6],
  ![2, 3, 5, 7],
  ![2, 3, 5, 8],
  ![2, 3, 5, 9],
  ![2, 3, 6, 7],
  ![2, 3, 6, 8],
  ![2, 3, 6, 9],
  ![2, 3, 7, 8],
  ![2, 3, 7, 9],
  ![2, 3, 8, 9],
  ![2, 4, 5, 6],
  ![2, 4, 5, 7],
  ![2, 4, 5, 8],
  ![2, 4, 5, 9],
  ![2, 4, 6, 7],
  ![2, 4, 6, 8],
  ![2, 4, 6, 9],
  ![2, 4, 7, 8],
  ![2, 4, 7, 9],
  ![2, 4, 8, 9],
  ![2, 5, 6, 7],
  ![2, 5, 6, 8],
  ![2, 5, 6, 9],
  ![2, 5, 7, 8],
  ![2, 5, 7, 9],
  ![2, 5, 8, 9],
  ![2, 6, 7, 8],
  ![2, 6, 7, 9],
  ![2, 6, 8, 9],
  ![2, 7, 8, 9],
  ![3, 4, 5, 6],
  ![3, 4, 5, 7],
  ![3, 4, 5, 8],
  ![3, 4, 5, 9],
  ![3, 4, 6, 7],
  ![3, 4, 6, 8],
  ![3, 4, 6, 9],
  ![3, 4, 7, 8],
  ![3, 4, 7, 9],
  ![3, 4, 8, 9],
  ![3, 5, 6, 7],
  ![3, 5, 6, 8],
  ![3, 5, 6, 9],
  ![3, 5, 7, 8],
  ![3, 5, 7, 9],
  ![3, 5, 8, 9],
  ![3, 6, 7, 8],
  ![3, 6, 7, 9],
  ![3, 6, 8, 9],
  ![3, 7, 8, 9],
  ![4, 5, 6, 7],
  ![4, 5, 6, 8],
  ![4, 5, 6, 9],
  ![4, 5, 7, 8],
  ![4, 5, 7, 9],
  ![4, 5, 8, 9],
  ![4, 6, 7, 8],
  ![4, 6, 7, 9],
  ![4, 6, 8, 9],
  ![4, 7, 8, 9],
  ![5, 6, 7, 8],
  ![5, 6, 7, 9],
  ![5, 6, 8, 9],
  ![5, 7, 8, 9],
  ![6, 7, 8, 9]
]

theorem quadrupleArray_size : quadrupleArray.size = 210 := by decide +kernel

def quadruple (i : Fin 210) : Fin 4 → Fin 10 :=
  quadrupleArray[i.val]'(by rw [quadrupleArray_size]; exact i.isLt)

theorem quadruple_strictMono : ∀ i : Fin 210, StrictMono (quadruple i) := by
  decide +kernel

theorem quadruple_injective : Function.Injective quadruple := by
  decide +kernel

/-- Coefficients on the increasing quadruples, least significant bit first. -/
def coefficientWord : Nat := 0x1d74239119236cff2cabddd5c0da56a4bf066e6556c887deab2d

def coordinateProjection (s : Fin 4 → Fin 10) : U →ₗ[F] (Fin 4 → F) where
  toFun v := fun i => v (s i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The exact alternating form specified by the packed coefficient word. -/
def quartic : Form :=
  ∑ i : Fin 210, if coefficientWord.testBit i.val then
    Matrix.detRowAlternating.compLinearMap (coordinateProjection (quadruple i)) else 0

/-- Contraction in the first two arguments, interpreted as a map to the dual. -/
def contraction (Q : Form) (v w : U) : U →ₗ[F] Module.Dual F U :=
  LinearMap.mk₂ F (fun x y => Q ![v, w, x, y])
    (fun x y z => ((Q.curryLeft v).curryLeft w).map_vecCons_add ![z] x y)
    (fun r x y => ((Q.curryLeft v).curryLeft w).map_vecCons_smul ![y] r x)
    (fun x y z => (((Q.curryLeft v).curryLeft w).curryLeft x).map_vecCons_add ![] y z)
    (fun r x y => (((Q.curryLeft v).curryLeft w).curryLeft x).map_vecCons_smul ![] r y)

@[simp] theorem contraction_apply (Q : Form) (v w x y : U) :
    contraction Q v w x y = Q ![v, w, x, y] := rfl

/-- Ordinary bilinear rank of the contraction. -/
noncomputable def contractionRank (Q : Form) (v w : U) : Nat :=
  Module.finrank F (contraction Q v w).range

/-- Number of second arguments giving each bilinear rank. -/
noncomputable def rankDistribution (Q : Form) (v : U) (r : Nat) : Nat :=
  Nat.card {w : U // contractionRank Q v w = r}

/-- Preservation is quantified over all four arguments. -/
def Preserves (Q : Form) (g : U ≃ₗ[F] U) : Prop :=
  ∀ v w x y, Q ![g v, g w, g x, g y] = Q ![v, w, x, y]

theorem preserves_refl (Q : Form) : Preserves Q (LinearEquiv.refl F U) := by
  intro v w x y
  rfl

theorem Preserves.symm {Q : Form} {g : U ≃ₗ[F] U} (hg : Preserves Q g) :
    Preserves Q g.symm := by
  intro v w x y
  simpa using (hg (g.symm v) (g.symm w) (g.symm x) (g.symm y)).symm

theorem Preserves.trans {Q : Form} {g h : U ≃ₗ[F] U}
    (hg : Preserves Q g) (hh : Preserves Q h) : Preserves Q (g.trans h) := by
  intro v w x y
  exact (hh (g v) (g w) (g x) (g y)).trans (hg v w x y)

attribute [local irreducible] quartic

/-- The full linear stabilizer of the specified quartic. -/
def quarticStabilizer : Subgroup (U ≃ₗ[F] U) where
  carrier := {g | Preserves quartic g}
  one_mem' := preserves_refl quartic
  mul_mem' {_g h} hg hh v w x y :=
    (hg (h v) (h w) (h x) (h y)).trans (hh v w x y)
  inv_mem' hg := hg.symm

/-- Pullback on the dual transports the full contraction image. -/
theorem contraction_range_transport {Q : Form} {g : U ≃ₗ[F] U}
    (hg : Preserves Q g) (v w : U) :
    ((contraction Q (g v) (g w)).range).map g.dualMap.toLinearMap =
      (contraction Q v w).range := by
  have heq : g.dualMap.toLinearMap.comp (contraction Q (g v) (g w)) =
      (contraction Q v w).comp g.symm.toLinearMap := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change Q ![g v, g w, x, g y] = Q ![v, w, g.symm x, y]
    simpa using hg v w (g.symm x) y
  rw [← LinearMap.range_comp, heq]
  exact LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr g.symm.surjective)

/-- Every preserving linear equivalence preserves all contraction ranks. -/
theorem contractionRank_invariant {Q : Form} {g : U ≃ₗ[F] U}
    (hg : Preserves Q g) (v w : U) :
    contractionRank Q (g v) (g w) = contractionRank Q v w := by
  unfold contractionRank
  rw [← g.dualMap.finrank_map_eq, contraction_range_transport hg]

/-- Every preserving linear equivalence preserves the entire rank histogram. -/
theorem rankDistribution_invariant {Q : Form} {g : U ≃ₗ[F] U}
    (hg : Preserves Q g) (v : U) : rankDistribution Q (g v) = rankDistribution Q v := by
  funext r
  apply Eq.symm
  exact Nat.card_congr (g.toEquiv.subtypeEquiv (fun w => by
    change contractionRank Q v w = r ↔ contractionRank Q (g v) (g w) = r
    rw [contractionRank_invariant hg]))

/-- The distinguishing histogram, including zero entries at all other ranks. -/
def pointDistribution (r : Nat) : Nat :=
  if r = 0 then 2 else if r = 4 then 42 else if r = 6 then 420 else
    if r = 8 then 560 else 0

/-- Decode a binary integer in the standard coordinate basis. -/
def vector (n : Nat) : U := fun i => if n.testBit i.val then 1 else 0

/-- The 22 candidate intrinsic points in increasing packed order. -/
def pointWord (i : Fin 22) : Nat :=
  ![8, 24, 44, 76, 79, 94, 147, 158, 161, 166, 298, 323, 333, 335,
    557, 593, 710, 721, 817, 839, 999, 1018] i

def sortedPoint (i : Fin 22) : U := vector (pointWord i)

/-- The explicit marking into the repository's literal 22-point design. -/
def pointMarking : Equiv.Perm (Fin 22) where
  toFun := ![0, 1, 2, 12, 6, 3, 11, 7, 20, 4, 8, 15, 5, 21, 13, 9, 16, 19, 18, 17, 14, 10]
  invFun := ![0, 1, 2, 5, 9, 12, 4, 7, 10, 15, 21, 6, 3, 14, 20, 11, 16, 19, 18, 17, 8, 13]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Vectors indexed by the repository's point labels. -/
def point (i : Fin 22) : U := sortedPoint (pointMarking.symm i)

theorem point_marking (i : Fin 22) : point (pointMarking i) = sortedPoint i := by
  simp [point]

theorem point_injective : Function.Injective point := by
  decide +kernel

/-- Explicit expressions for the ten standard basis vectors in the marked points. -/
def basisPointMask (i : Fin 10) : Nat :=
  ![75, 1709, 151, 1, 3, 146, 1584, 1720, 1741, 1144] i

def basisPointSet (i : Fin 10) : Finset (Fin 22) :=
  Finset.univ.filter (fun j => (basisPointMask i).testBit j.val)

theorem basisPointSet_sum : ∀ i : Fin 10,
    ∑ j ∈ basisPointSet i, point j = Pi.single i (1 : F) := by
  decide +kernel

/-- The literal 22-point configuration spans the entire ten-dimensional space. -/
theorem point_span : Submodule.span F (Set.range point) = ⊤ := by
  apply top_unique
  rw [← (Pi.basisFun F (Fin 10)).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  rw [Pi.basisFun_apply, ← basisPointSet_sum i]
  exact Submodule.sum_mem _ (fun j _ => Submodule.subset_span ⟨j, rfl⟩)

/-- A six-subset of the marked points whose vector sum is zero. -/
def IsHexad (B : Finset (Fin 22)) : Prop := B.card = 6 ∧ ∑ i ∈ B, point i = 0

end BinaryQuarticMathieu
