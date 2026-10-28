module
public import Theory.SpecificGroups.Triality.OddFundamentalCentralizer.Centralizer.Geometry.Specialization
/-!
# Integral adjoint coordinates for the odd D4 comparison

The four Cartan columns are the signed simple coroot matrices, with bipartite
signs `(1,-1,1,1)`. The other columns are signed natural orthogonal root
matrices, ordered exactly as `Geometry.coordinateEquiv`. Sparse rows retain
all 28 columns and both signs of every root. The certificates compare the
linear and quadratic Geck coefficients with commutators and negative double
multiplication by the natural nilpotent root matrices. Thus they apply before
any characteristic specialization, including characteristic three.

Sources: GLS3 §§2.4, 2.6–2.7 (`refs/KGroup/GLS3/chapter2.tex`); the comparison
needed for Aschbacher–Smith A.2.17, printed pp.38–39.
-/

@[expose] public section
noncomputable section
open Matrix
namespace Triality.Standard.OddFundamentalCentralizer.ElementaryIndex.HighestUnipotent.OrthogonalComparison
open Geometry.Integral
abbrev NaturalIndex := Fin 4 ⊕ Fin 4
abbrev NaturalMatrix (R : Type*) := Matrix NaturalIndex NaturalIndex R

def coordinateRows (a b : NaturalIndex) : List (Ix × ℤ) :=
  (![
    ![[(0, 1)], [(5, -1)], [(9, 1)], [(13, -1)], [], [(4, -1)], [(8, -1)], [(12, -1)]],
    ![[(6, 1)], [(0, -1), (1, -1)], [(17, 1)], [(21, -1)], [(4, 1)], [], [(16, -1)], [(20, -1)]],
    ![[(10, 1)], [(18, -1)], [(1, 1), (2, 1), (3, 1)], [(25, -1)], [(8, 1)], [(16, 1)], [], [(24, -1)]],
    ![[(14, 1)], [(22, -1)], [(26, 1)], [(2, -1), (3, 1)], [(12, 1)], [(20, 1)], [(24, 1)], []],
    ![[], [(7, -1)], [(11, 1)], [(15, -1)], [(0, -1)], [(6, -1)], [(10, -1)], [(14, -1)]],
    ![[(7, 1)], [], [(19, -1)], [(23, 1)], [(5, 1)], [(0, 1), (1, 1)], [(18, 1)], [(22, 1)]],
    ![[(11, -1)], [(19, 1)], [], [(27, -1)], [(9, -1)], [(17, -1)], [(1, -1), (2, -1), (3, -1)], [(26, -1)]],
    ![[(15, 1)], [(23, -1)], [(27, 1)], [], [(13, 1)], [(21, 1)], [(25, 1)], [(2, 1), (3, -1)]]
  ]) (finSumFinEquiv a) (finSumFinEquiv b)

def basisMatrix (c : Ix) : NaturalMatrix ℤ := fun a b => rowEntry (coordinateRows a b) c

def positions (i : Fin 4) (b : Bool) : (NaturalIndex × NaturalIndex) × (NaturalIndex × NaturalIndex) :=
  if b then
    ![((.inl 0, .inl 1), (.inr 1, .inr 0)),
      ((.inl 1, .inl 2), (.inr 2, .inr 1)),
      ((.inl 2, .inl 3), (.inr 3, .inr 2)),
      ((.inl 2, .inr 3), (.inl 3, .inr 2))] i
  else
    ![((.inl 1, .inl 0), (.inr 0, .inr 1)),
      ((.inl 2, .inl 1), (.inr 1, .inr 2)),
      ((.inl 3, .inl 2), (.inr 2, .inr 3)),
      ((.inr 3, .inl 2), (.inr 2, .inl 3))] i

def naturalGenerator (i : Fin 4) (b : Bool) : NaturalMatrix ℤ :=
  single (positions i b).1.1 (positions i b).1.2 1 -
    single (positions i b).2.1 (positions i b).2.2 1

def leftEntry (i : Fin 4) (d : Bool) (B : NaturalMatrix ℤ) (a b : NaturalIndex) : ℤ :=
  (if a = (positions i d).1.1 then B (positions i d).1.2 b else 0) -
    (if a = (positions i d).2.1 then B (positions i d).2.2 b else 0)

def rightEntry (i : Fin 4) (d : Bool) (B : NaturalMatrix ℤ) (a b : NaturalIndex) : ℤ :=
  (if b = (positions i d).1.2 then B a (positions i d).1.1 else 0) -
    (if b = (positions i d).2.2 then B a (positions i d).2.1 else 0)

theorem coefficient_identity (i : Fin 4) (d : Bool)
    (a b : NaturalIndex) (c : Ix) :
    rowProduct (coordinateRows a b) (linear i d) c =
      leftEntry i d (basisMatrix c) a b - rightEntry i d (basisMatrix c) a b ∧
    rowProduct (coordinateRows a b) (quadratic i d) c =
      -rightEntry i d (leftEntry i d (basisMatrix c)) a b := by
  fin_cases i <;> cases d <;> revert a b c <;> decide +kernel

theorem leftEntry_eq (i : Fin 4) (d : Bool) (B : NaturalMatrix ℤ) :
    leftEntry i d B = naturalGenerator i d * B := by
  ext a b
  simp only [naturalGenerator, sub_mul, Matrix.sub_apply, leftEntry]
  congr 1 <;> (split_ifs with h; subst a; simp; simp [h])

theorem rightEntry_eq (i : Fin 4) (d : Bool) (B : NaturalMatrix ℤ) :
    rightEntry i d B = B * naturalGenerator i d := by
  ext a b
  simp only [naturalGenerator, mul_sub, Matrix.sub_apply, rightEntry]
  congr 1 <;> (split_ifs with h; subst b; simp; simp [h])

theorem rowEntry_mul (l : List (Ix × ℤ)) (B : Rows) (c : Ix) :
    (∑ k, rowEntry l k * rowEntry (B k) c) = rowProduct l B c := by
  induction l with
  | nil => simp [rowEntry, rowProduct]
  | cons x l ih =>
    rcases x with ⟨k,a⟩
    simp [rowEntry, add_mul, Finset.sum_add_distrib, ih, rowProduct, ite_mul]

end Triality.Standard.OddFundamentalCentralizer.ElementaryIndex.HighestUnipotent.OrthogonalComparison
