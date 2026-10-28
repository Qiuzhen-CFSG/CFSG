module

public import Theory.Mathieu.M24.Basic
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.Tactic.FinCases
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The ATLAS words with the native M₂₄ composition convention

The seven words of John Bray's ATLAS presentation `M24G1-P1` are first
converted to positive words using the square and cube equations, then reversed
for left composition. Both transformations are proved. The actual native
permutations satisfy these words, giving a homomorphism `toCarrier`.
No injectivity or abstract order bound is asserted here.

The same positive words can be checked on the untransposed ATLAS row matrices.
Transposition and the universal map to a monoid connect those independent
matrix checks to a column action once the carrier map is known to be bijective.

Source: https://brauer.maths.qmul.ac.uk/Atlas/v3/pres/M24G1-P1
See `source/README.md` for conventions, attribution, and remaining obligations.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation
open Sporadic.Mathieu

/-- Positive ATLAS words in the published row-action order. -/
def rowRelatorValues {G : Type*} [Monoid G] (a b : G) : Fin 7 → G :=
  ![a ^ 2, b ^ 3, (a * b) ^ 23,
    (a * b ^ 2 * a * b) ^ 12,
    (a * b ^ 2 * a * b ^ 2 * a * b * a * b) ^ 5,
    (a * b * a * b * a * b ^ 2) ^ 3 * (a * b * a * b ^ 2 * a * b ^ 2) ^ 3,
    (a * b * (a * b * a * b ^ 2) ^ 3) ^ 4]

/-- All seven source relators, with commutator convention `a⁻¹ b⁻¹ a b`. -/
def atlasRelatorValues {G : Type*} [Group G] (a b : G) : Fin 7 → G :=
  ![a ^ 2, b ^ 3, (a * b) ^ 23,
    (a⁻¹ * b⁻¹ * a * b) ^ 12,
    (a⁻¹ * (b * a * b)⁻¹ * a * (b * a * b)) ^ 5,
    (a * b * a * b * a * b⁻¹) ^ 3 * (a * b * a * b⁻¹ * a * b⁻¹) ^ 3,
    (a * b * (a * b * a * b⁻¹) ^ 3) ^ 4]

/-- The first two equations justify replacing the inverses in the source words. -/
theorem rowRelatorValues_eq_atlas {G : Type*} [Group G] (a b : G)
    (ha : a ^ 2 = 1) (hb : b ^ 3 = 1) (i : Fin 7) :
    rowRelatorValues a b i = atlasRelatorValues a b i := by
  have haInv : a⁻¹ = a := by
    apply mul_left_cancel (a := a)
    simp [← pow_two, ha]
  have hbInv : b⁻¹ = b ^ 2 := by
    apply mul_left_cancel (a := b)
    rw [mul_inv_cancel, ← pow_succ', hb]
  fin_cases i <;> simp [rowRelatorValues, atlasRelatorValues, mul_inv_rev,
    haInv, hbInv, mul_assoc]

/-- Reversed positive words, for native permutations and column matrices. -/
def relatorValues {G : Type*} [Monoid G] (a b : G) : Fin 7 → G :=
  ![a ^ 2, b ^ 3, (b * a) ^ 23,
    (b * a * b ^ 2 * a) ^ 12,
    (b * a * b * a * b ^ 2 * a * b ^ 2 * a) ^ 5,
    (b ^ 2 * a * b ^ 2 * a * b * a) ^ 3 * (b ^ 2 * a * b * a * b * a) ^ 3,
    ((b ^ 2 * a * b * a) ^ 3 * b * a) ^ 4]

/-- Reversal here is exactly passage through the opposite monoid. -/
theorem relatorValues_eq_reverse {G : Type*} [Monoid G] (a b : G) (i : Fin 7) :
    relatorValues a b i =
      MulOpposite.unop (rowRelatorValues (MulOpposite.op a) (MulOpposite.op b) i) := by
  fin_cases i <;> simp [relatorValues, rowRelatorValues, mul_assoc]

/-- Seven equations in left-composition order; no presentation exactness claim. -/
def Relations {G : Type*} [Monoid G] (a b : G) : Prop :=
  ∀ i, relatorValues a b i = 1

/-- Seven equations on the original untransposed ATLAS row matrices. -/
def RowRelations {G : Type*} [Monoid G] (a b : G) : Prop :=
  ∀ i, rowRelatorValues a b i = 1

theorem map_relatorValues {G H : Type*} [Monoid G] [Monoid H]
    (f : G →* H) (a b : G) (i : Fin 7) :
    f (relatorValues a b i) = relatorValues (f a) (f b) i := by
  fin_cases i <;> simp [relatorValues]

/-- Transposition converts all seven row words to the native word convention. -/
theorem transpose_rowRelatorValues {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) (ZMod 2)) (i : Fin 7) :
    (rowRelatorValues A B i).transpose = relatorValues A.transpose B.transpose i := by
  fin_cases i <;> simp [rowRelatorValues, relatorValues, Matrix.transpose_mul,
    Matrix.transpose_pow, mul_assoc]

theorem RowRelations.transpose {d : ℕ} {A B : Matrix (Fin d) (Fin d) (ZMod 2)}
    (h : RowRelations A B) : Relations A.transpose B.transpose := by
  intro i
  rw [← transpose_rowRelatorValues, h i, Matrix.transpose_one]

/-- The explicit relations used to form the abstract presented group. -/
def relators : Set (FreeGroup (Fin 2)) :=
  Set.range (relatorValues (FreeGroup.of 0) (FreeGroup.of 1))

/-- The abstract presentation, whose order remains a separate obligation. -/
abbrev UniversalGroup := PresentedGroup relators

/-- Evaluate the presented group in a group satisfying the seven equations. -/
def toGroup {G : Type*} [Group G] (a b : G) (h : Relations a b) :
    UniversalGroup →* G :=
  PresentedGroup.toGroup (f := ![a, b]) (by
    rintro r ⟨i, rfl⟩
    rw [map_relatorValues]
    simpa using h i)

@[simp] theorem toGroup_zero {G : Type*} [Group G] (a b : G) (h : Relations a b) :
    toGroup a b h (PresentedGroup.of 0) = a :=
  PresentedGroup.toGroup.of _

@[simp] theorem toGroup_one {G : Type*} [Group G] (a b : G) (h : Relations a b) :
    toGroup a b h (PresentedGroup.of 1) = b :=
  PresentedGroup.toGroup.of _


/-- The first two relations supply inverses, so the universal map also takes
values in an arbitrary monoid. -/
def toMonoid {G : Type*} [Monoid G] (a b : G) (h : Relations a b) :
    UniversalGroup →* G :=
  let ua : Gˣ :=
    ⟨a, a, by simpa [relatorValues, pow_two] using h 0,
      by simpa [relatorValues, pow_two] using h 0⟩
  let ub : Gˣ :=
    ⟨b, b ^ 2, by simpa [relatorValues, pow_succ'] using h 1,
      by simpa [relatorValues, pow_succ] using h 1⟩
  (Units.coeHom G).comp (toGroup ua ub (by
    intro i
    apply Units.ext
    change Units.coeHom G (relatorValues ua ub i) = Units.coeHom G 1
    rw [map_relatorValues, map_one]
    exact h i))

@[simp] theorem toMonoid_zero {G : Type*} [Monoid G] (a b : G) (h : Relations a b) :
    toMonoid a b h (PresentedGroup.of 0) = a := by
  simp [toMonoid]

@[simp] theorem toMonoid_one {G : Type*} [Monoid G] (a b : G) (h : Relations a b) :
    toMonoid a b h (PresentedGroup.of 1) = b := by
  simp [toMonoid]

/-- The unchanged first native standard generator. -/
def a : M24 := ⟨m24GeneratorA, m24GeneratorA_mem⟩
/-- The unchanged second native standard generator. -/
def b : M24 := ⟨m24GeneratorB, m24GeneratorB_mem⟩

set_option maxRecDepth 10000 in
/-- All seven equations on the literal Witt-design permutations, checked in the kernel. -/
theorem carrier_relations : Relations a b := by
  intro i
  apply Subtype.ext
  change M24.subtype (relatorValues a b i) = M24.subtype 1
  rw [map_relatorValues, map_one]
  change relatorValues m24GeneratorA m24GeneratorB i = 1
  revert i
  decide +kernel

/-- The marked homomorphism to the actual Witt-design automorphism group. -/
noncomputable def toCarrier : UniversalGroup →* M24 := toGroup a b carrier_relations

@[simp] theorem toCarrier_zero : toCarrier (PresentedGroup.of 0) = a := toGroup_zero _ _ _
@[simp] theorem toCarrier_one : toCarrier (PresentedGroup.of 1) = b := toGroup_one _ _ _

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation
