module

public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.Three.Descent.ExceptionalTorus.Coordinates
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Cyclotomic.WeylAction
import all Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Cyclotomic.WeylAction

/-!
# The Weyl word for the marked nonsplit torus

The word `[0,1,0,2,1,0,2,1,3,2,1,0]` followed by exceptional duality
has square minus twice the identity on the coroot lattice. Prepending
the m-th power of the opposition word gives the signed exponent `(-2)^m`.
The proof extends the checked simple-reflection calculation in
`Cyclotomic.WeylAction` to this literal word. Its private implementation
is intentionally shared through `import all`; no private name enters the
public interface and the existing module remains unchanged.

Integer certificates are split into four-letter blocks to avoid repeated
expansion of a twelve-letter matrix product. `normalizer_twist` is an
equation in the actual closed F₄ carrier, not only on its root lattice.

Sources: Steinberg, Lectures on Chevalley Groups, Lemma 19;
GLS3 Example 2.6.3 and Table 4.7.3A.
-/

@[expose] public section
open Theory.AlgebraicGroup
open scoped Matrix
namespace ReeF4.CentralCovers.OddPrimary.Three.Descent.ExceptionalTorus
open ReeF4.CentralCovers.OddPrimary.Cyclotomic
noncomputable section
variable {F : Type*} [Field F] [IsAlgClosed F]

def baseWord : List (Fin 4) :=
  [0, 1, 0, 2] ++ [1, 0, 2, 1] ++ [3, 2, 1, 0]

def wordElement (l : List (Fin 4)) : AlgebraicPoints F :=
  (l.map (simpleWeyl (F := F))).prod

def opposition : AlgebraicPoints F :=
  (simpleWeyl 0 * simpleWeyl 1 * simpleWeyl 2 * simpleWeyl 3) ^ 6

def normalizer (m : ℕ) : AlgebraicPoints F :=
  opposition ^ m * wordElement baseWord

private def wordMatrix (l : List (Fin 4)) : Matrix (Fin 4) (Fin 4) ℤ :=
  (l.map Cyclotomic.reflectionMatrix).prod

private theorem word_conjugation (l : List (Fin 4)) (u : Fin 4 → Fˣ) :
    wordElement l * diagonal u * (wordElement l)⁻¹ =
      diagonal (Cyclotomic.latticeAction (wordMatrix l) u) := by
  induction l generalizing u with
  | nil => simp [wordElement, wordMatrix, Cyclotomic.latticeAction_one]
  | cons i l ih =>
    simpa only [wordElement, wordMatrix, List.map_cons, List.prod_cons] using
      Cyclotomic.conjugation_mul (Cyclotomic.simpleWeyl_diagonal i) ih u

private theorem base_matrix : wordMatrix baseWord =
    !![-1,-1,2,0; -3,0,2,0; -2,0,1,1; -1,0,1,0] := by
  have h0 : wordMatrix [0,1,0,2] =
      !![0,1,-2,2; -1,2,-2,2; 0,1,-1,1; 0,0,0,1] := by decide
  have h1 : wordMatrix [1,0,2,1] =
      !![0,-1,2,0; 1,-2,2,2; 1,-1,1,1; 0,0,0,1] := by decide
  have h2 : wordMatrix [3,2,1,0] =
      !![-1,1,0,0; -1,0,2,0; -1,0,1,1; -1,0,1,0] := by decide
  change wordMatrix ([0,1,0,2] ++ [1,0,2,1] ++ [3,2,1,0]) = _
  simp only [wordMatrix, List.map_append, List.prod_append] at *
  rw [h0, h1, h2]
  decide

private theorem base_twist_matrix :
    wordMatrix baseWord * Cyclotomic.exceptionalMatrix =
      !![0,2,-2,-2; 0,2,0,-6; 1,1,0,-4; 0,1,0,-2] := by
  rw [base_matrix]
  decide

private theorem normalizer_conjugation (m : ℕ) (u : Fin 4 → Fˣ) :
    normalizer m * diagonal u * (normalizer m)⁻¹ =
      diagonal (Cyclotomic.latticeAction
        (((-1 : ℤ)^m) • wordMatrix baseWord) u) := by
  have ho : ∀ v : Fin 4 → Fˣ,
      opposition * diagonal v * opposition⁻¹ =
        diagonal (Cyclotomic.latticeAction (-1) v) := by
    intro v
    rw [Cyclotomic.latticeAction_neg, Cyclotomic.latticeAction_one]
    exact Cyclotomic.opposition_diagonal v
  have hp := Cyclotomic.conjugation_mul (Cyclotomic.conjugation_pow ho m)
    (word_conjugation baseWord) u
  change normalizer m * diagonal u * (normalizer m)⁻¹ = _ at hp
  rw [show (-1 : Matrix (Fin 4) (Fin 4) ℤ)^m =
    ((-1 : ℤ)^m) • (1 : Matrix (Fin 4) (Fin 4) ℤ) by simp,
    Matrix.smul_mul, Matrix.one_mul] at hp
  exact hp

variable [CharP F 2]

theorem normalizer_twist (m : ℕ) (u : Fin 4 → Fˣ) :
    normalizer m * (algebraicReeTwist m).onPoints (diagonal u) * (normalizer m)⁻¹ =
      diagonal (twistedCoordinates (signedExponent m) u) := by
  have ht : (algebraicReeTwist m).onPoints (diagonal u) =
      diagonal (Cyclotomic.latticeAction (Cyclotomic.exceptionalMatrix ^ (2*m+1)) u) :=
    (DFunLike.congr_fun (algebraicReeTwist_onPoints m) (diagonal u)).trans
      (Cyclotomic.exceptional_power_diagonal (2*m+1) u)
  rw [ht, normalizer_conjugation, ← Cyclotomic.latticeAction_mul,
    Cyclotomic.exceptional_matrix_odd, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, ← mul_pow, show (-1 : ℤ)*2 = -2 by decide, base_twist_matrix]
  congr 1
  ext i
  fin_cases i <;> simp [Cyclotomic.latticeAction, twistedCoordinates, signedExponent,
    Fin.prod_univ_four, mul_comm ((-2 : ℤ)^m)]

end
end ReeF4.CentralCovers.OddPrimary.Three.Descent.ExceptionalTorus
