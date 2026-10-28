module

public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

/-!
# A checked finite lattice embedding for the middle C2 pair

The explicit integral operators on 52 and 26 coordinates admit a sparse
intertwiner with 29 nonzero entries. Its explicit recovery map composes to
four times the identity. Checking the first two coefficients proves the
whole quadratic curve identity over every commutative ring; coordinate
recovery gives injectivity over every field in which two is nonzero.

`Descent.actionOfComparisons` applies this embedding to the literal F4 pair
subgroup. Its two coordinate comparisons are still required: no identification
of these tables with either actual Geck representation is asserted here.
`Numbering` and `source/` specify their intended root and Cartan coordinates.
No irreducibility or division by three is used.

Sources: the Geck root-string formulas in `IntegralGeckConstruction.lean`,
GLS3 §2.6.2 (`refs/KGroup/GLS3/chapter2.tex`), and the F4 inclusion in
Aschbacher--Smith A.2.17, printed p.39 (`refs/quasithin.pdf`).
-/

@[expose] public section
noncomputable section
namespace TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.MiddleC2.FiniteLattice
variable (R : Type*) [CommRing R]

def sourceFirst0 (v : Fin 52 → R) : Fin 52 → R :=
  ![0,
    v 24,
    0,
    0,
    0,
    0,
    v 5,
    0,
    0,
    0,
    0,
    0,
    v 9,
    v 10,
    v 11,
    0,
    0,
    0,
    v 17,
    0,
    0,
    0,
    0,
    0,
    0,
    v 22,
    v 23,
    0,
    0,
    0,
    0,
    v 0 + (2 : R) * v 1 + (2 : R) * v 2,
    v 29,
    v 30,
    0,
    0,
    0,
    0,
    v 37,
    0,
    0,
    0,
    0,
    0,
    v 41,
    v 42,
    v 43,
    0,
    0,
    0,
    v 49,
    0]

def sourceSecond0 (v : Fin 52 → R) : Fin 52 → R :=
  ![0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    v 24,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0]

def sourceFirst1 (v : Fin 52 → R) : Fin 52 → R :=
  ![0,
    v 31,
    0,
    0,
    0,
    v 6,
    0,
    0,
    0,
    v 12,
    v 13,
    v 14,
    0,
    0,
    0,
    0,
    0,
    v 18,
    0,
    0,
    0,
    0,
    v 25,
    v 26,
    v 0 + (2 : R) * v 1 + (2 : R) * v 2,
    0,
    0,
    0,
    0,
    v 32,
    v 33,
    0,
    0,
    0,
    0,
    0,
    0,
    v 38,
    0,
    0,
    0,
    v 44,
    v 45,
    v 46,
    0,
    0,
    0,
    0,
    0,
    v 50,
    0,
    0]

def sourceSecond1 (v : Fin 52 → R) : Fin 52 → R :=
  ![0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    v 31,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0]

def sourceFirst2 (v : Fin 52 → R) : Fin 52 → R :=
  ![0,
    0,
    v 26,
    0,
    0,
    0,
    0,
    v 6,
    0,
    (2 : R) * v 7,
    v 8,
    0,
    0,
    0,
    0,
    v 13,
    v 14,
    (2 : R) * v 16,
    0,
    0,
    0,
    0,
    v 20,
    v 21,
    (2 : R) * v 23,
    0,
    0,
    v 25,
    0,
    v 1 + (2 : R) * v 2 + v 3,
    v 28,
    0,
    v 31,
    0,
    (2 : R) * v 32,
    v 33,
    0,
    0,
    0,
    v 38,
    0,
    (2 : R) * v 39,
    v 40,
    0,
    0,
    0,
    0,
    v 45,
    v 46,
    (2 : R) * v 48,
    0,
    0]

def sourceSecond2 (v : Fin 52 → R) : Fin 52 → R :=
  ![0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    v 6,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    v 14,
    0,
    0,
    0,
    0,
    0,
    0,
    v 21,
    0,
    0,
    0,
    0,
    v 26,
    0,
    0,
    0,
    0,
    v 31,
    0,
    0,
    0,
    0,
    0,
    0,
    v 38,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    v 46,
    0,
    0]

def sourceFirst3 (v : Fin 52 → R) : Fin 52 → R :=
  ![0,
    0,
    v 29,
    0,
    0,
    0,
    (2 : R) * v 7,
    v 9,
    v 10,
    0,
    0,
    0,
    0,
    v 15,
    (2 : R) * v 16,
    0,
    v 17,
    0,
    0,
    0,
    v 22,
    (2 : R) * v 23,
    0,
    v 24,
    0,
    v 27,
    v 1 + (2 : R) * v 2 + v 3,
    0,
    v 30,
    0,
    0,
    (2 : R) * v 32,
    v 34,
    v 35,
    0,
    0,
    0,
    0,
    (2 : R) * v 39,
    v 41,
    v 42,
    0,
    0,
    0,
    0,
    v 47,
    (2 : R) * v 48,
    0,
    v 49,
    0,
    0,
    0]

def sourceSecond3 (v : Fin 52 → R) : Fin 52 → R :=
  ![0,
    0,
    0,
    0,
    0,
    0,
    v 9,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    v 17,
    0,
    0,
    0,
    0,
    0,
    0,
    v 24,
    0,
    0,
    0,
    0,
    v 29,
    0,
    0,
    0,
    0,
    v 34,
    0,
    0,
    0,
    0,
    0,
    0,
    v 41,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    v 49,
    0,
    0,
    0,
    0,
    0]

def sourceFirst (s k : Bool) : (Fin 52 → R) → (Fin 52 → R) :=
  if k then if s then sourceFirst0 R else sourceFirst1 R
  else if s then sourceFirst2 R else sourceFirst3 R

def sourceSecond (s k : Bool) : (Fin 52 → R) → (Fin 52 → R) :=
  if k then if s then sourceSecond0 R else sourceSecond1 R
  else if s then sourceSecond2 R else sourceSecond3 R

def targetFirst0 (v : Fin 26 → R) : Fin 26 → R :=
  ![0,
    0,
    0,
    0,
    0,
    v 4,
    0,
    0,
    0,
    v 8,
    0,
    0,
    0,
    v 12,
    0,
    0,
    0,
    v 15,
    v 16,
    0,
    0,
    0,
    0,
    v 22,
    0,
    0]

def targetSecond0 (_v : Fin 26 → R) : Fin 26 → R :=
  ![0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0]

def targetFirst1 (v : Fin 26 → R) : Fin 26 → R :=
  ![0,
    0,
    0,
    0,
    v 5,
    0,
    0,
    0,
    v 9,
    0,
    0,
    0,
    v 13,
    0,
    0,
    v 17,
    v 18,
    0,
    0,
    0,
    0,
    0,
    v 23,
    0,
    0,
    0]

def targetSecond1 (_v : Fin 26 → R) : Fin 26 → R :=
  ![0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0]

def targetFirst2 (v : Fin 26 → R) : Fin 26 → R :=
  ![0,
    v 13,
    0,
    0,
    v 3,
    0,
    v 5,
    0,
    v 7,
    0,
    v 9,
    0,
    0,
    0,
    0,
    (-1 : R) * v 0 + (-2 : R) * v 1,
    v 14,
    0,
    0,
    0,
    0,
    v 18,
    v 20,
    0,
    v 23,
    0]

def targetSecond2 (v : Fin 26 → R) : Fin 26 → R :=
  ![0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    (-1 : R) * v 13,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0]

def targetFirst3 (v : Fin 26 → R) : Fin 26 → R :=
  ![0,
    (-1 : R) * v 15,
    0,
    v 4,
    0,
    v 6,
    0,
    v 8,
    0,
    v 10,
    0,
    0,
    0,
    v 0 + (2 : R) * v 1,
    v 16,
    0,
    0,
    0,
    v 21,
    0,
    v 22,
    0,
    0,
    v 24,
    0,
    0]

def targetSecond3 (v : Fin 26 → R) : Fin 26 → R :=
  ![0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    (-1 : R) * v 15,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0]

def targetFirst (s k : Bool) : (Fin 26 → R) → (Fin 26 → R) :=
  if k then if s then targetFirst0 R else targetFirst1 R
  else if s then targetFirst2 R else targetFirst3 R

def targetSecond (s k : Bool) : (Fin 26 → R) → (Fin 26 → R) :=
  if k then if s then targetSecond0 R else targetSecond1 R
  else if s then targetSecond2 R else targetSecond3 R

def embeddingFun (v : Fin 26 → R) : Fin 52 → R :=
  ![(4 : R) * v 0,
    (-4 : R) * v 0,
    (2 : R) * v 0,
    0,
    (2 : R) * v 2,
    (-2 : R) * v 12,
    (-2 : R) * v 13,
    (-1 : R) * v 0 + (-2 : R) * v 1,
    (2 : R) * v 3,
    (2 : R) * v 15,
    (2 : R) * v 4,
    0,
    (2 : R) * v 17,
    (2 : R) * v 5,
    0,
    (2 : R) * v 6,
    0,
    0,
    0,
    (2 : R) * v 11,
    (2 : R) * v 7,
    0,
    (2 : R) * v 8,
    0,
    0,
    (2 : R) * v 9,
    0,
    (2 : R) * v 10,
    (2 : R) * v 14,
    0,
    (2 : R) * v 16,
    0,
    0,
    (2 : R) * v 18,
    0,
    (2 : R) * v 21,
    (2 : R) * v 19,
    0,
    0,
    0,
    (2 : R) * v 20,
    0,
    (2 : R) * v 22,
    0,
    0,
    (2 : R) * v 23,
    0,
    (2 : R) * v 24,
    0,
    0,
    0,
    (2 : R) * v 25]

def recovery (v : Fin 52 → R) : Fin 26 → R :=
  ![v 0,
    (-1 : R) * v 2 + (-2 : R) * v 7,
    (2 : R) * v 4,
    (2 : R) * v 8,
    (2 : R) * v 10,
    (2 : R) * v 13,
    (2 : R) * v 15,
    (2 : R) * v 20,
    (2 : R) * v 22,
    (2 : R) * v 25,
    (2 : R) * v 27,
    (2 : R) * v 19,
    (-2 : R) * v 5,
    (-2 : R) * v 6,
    (2 : R) * v 28,
    (2 : R) * v 9,
    (2 : R) * v 30,
    (2 : R) * v 12,
    (2 : R) * v 33,
    (2 : R) * v 36,
    (2 : R) * v 40,
    (2 : R) * v 35,
    (2 : R) * v 42,
    (2 : R) * v 45,
    (2 : R) * v 47,
    (2 : R) * v 51]

private theorem first_intertwines_0 (v : Fin 26 → R) :
    sourceFirst0 R (embeddingFun R v) = embeddingFun R (targetFirst0 R v) := by
  funext i
  fin_cases i <;> simp [sourceFirst0, targetFirst0, embeddingFun]
  all_goals ring

private theorem first_intertwines_1 (v : Fin 26 → R) :
    sourceFirst1 R (embeddingFun R v) = embeddingFun R (targetFirst1 R v) := by
  funext i
  fin_cases i <;> simp [sourceFirst1, targetFirst1, embeddingFun]
  all_goals ring

private theorem first_intertwines_2 (v : Fin 26 → R) :
    sourceFirst2 R (embeddingFun R v) = embeddingFun R (targetFirst2 R v) := by
  funext i
  fin_cases i <;> simp [sourceFirst2, targetFirst2, embeddingFun]
  all_goals ring

private theorem first_intertwines_3 (v : Fin 26 → R) :
    sourceFirst3 R (embeddingFun R v) = embeddingFun R (targetFirst3 R v) := by
  funext i
  fin_cases i <;> simp [sourceFirst3, targetFirst3, embeddingFun]
  all_goals ring

theorem first_intertwines (s k : Bool) (v : Fin 26 → R) :
    sourceFirst R s k (embeddingFun R v) = embeddingFun R (targetFirst R s k v) := by
  cases k <;> cases s
  · exact first_intertwines_3 R v
  · exact first_intertwines_2 R v
  · exact first_intertwines_1 R v
  · exact first_intertwines_0 R v

private theorem second_intertwines_0 (v : Fin 26 → R) :
    sourceSecond0 R (embeddingFun R v) = embeddingFun R (targetSecond0 R v) := by
  funext i
  fin_cases i <;> simp [sourceSecond0, targetSecond0, embeddingFun]

private theorem second_intertwines_1 (v : Fin 26 → R) :
    sourceSecond1 R (embeddingFun R v) = embeddingFun R (targetSecond1 R v) := by
  funext i
  fin_cases i <;> simp [sourceSecond1, targetSecond1, embeddingFun]

private theorem second_intertwines_2 (v : Fin 26 → R) :
    sourceSecond2 R (embeddingFun R v) = embeddingFun R (targetSecond2 R v) := by
  funext i
  fin_cases i <;> simp [sourceSecond2, targetSecond2, embeddingFun]

private theorem second_intertwines_3 (v : Fin 26 → R) :
    sourceSecond3 R (embeddingFun R v) = embeddingFun R (targetSecond3 R v) := by
  funext i
  fin_cases i <;> simp [sourceSecond3, targetSecond3, embeddingFun]

theorem second_intertwines (s k : Bool) (v : Fin 26 → R) :
    sourceSecond R s k (embeddingFun R v) = embeddingFun R (targetSecond R s k v) := by
  cases k <;> cases s
  · exact second_intertwines_3 R v
  · exact second_intertwines_2 R v
  · exact second_intertwines_1 R v
  · exact second_intertwines_0 R v

/-- The sparse integral map, as a linear map over any commutative ring. -/
def embedding : (Fin 26 → R) →ₗ[R] (Fin 52 → R) where
  toFun := embeddingFun R
  map_add' v w := by
    funext i
    fin_cases i <;> simp [embeddingFun]
    all_goals ring
  map_smul' a v := by
    funext i
    fin_cases i <;> simp [embeddingFun]
    all_goals ring

theorem recovery_embedding (v : Fin 26 → R) :
    recovery R (embedding R v) = (4 : R) • v := by
  change recovery R (embeddingFun R v) = _
  funext i
  fin_cases i <;> simp [recovery, embeddingFun]
  all_goals ring

variable (F : Type*) [Field F]
theorem embedding_injective (htwo : (2 : F) ≠ 0) :
    Function.Injective (embedding F) := by
  intro v w h
  have hh := congrArg (recovery F) h
  rw [recovery_embedding, recovery_embedding] at hh
  have hfour : (4 : F) ≠ 0 := by
    have he : (4 : F) = 2 * 2 := by ring
    rw [he]
    exact mul_ne_zero htwo htwo
  exact (smul_right_injective _ hfour) hh

def sourceCurve (s k : Bool) (t : R) (v : Fin 52 → R) : Fin 52 → R :=
  v + t • sourceFirst R s k v + t ^ 2 • sourceSecond R s k v

def targetCurve (s k : Bool) (t : R) (v : Fin 26 → R) : Fin 26 → R :=
  v + t • targetFirst R s k v + t ^ 2 • targetSecond R s k v

theorem curve_intertwines (s k : Bool) (t : R) (v : Fin 26 → R) :
    sourceCurve R s k t (embedding R v) =
      embedding R (targetCurve R s k t v) := by
  simp only [sourceCurve, targetCurve, map_add, map_smul]
  change embeddingFun R v + t • sourceFirst R s k (embeddingFun R v) +
      t ^ 2 • sourceSecond R s k (embeddingFun R v) = _
  rw [first_intertwines, second_intertwines]
  rfl

end TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.MiddleC2.FiniteLattice
