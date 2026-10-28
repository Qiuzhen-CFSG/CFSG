module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.LeftWeights.Characters
public import Theory.AlgebraicGroup.Representations.Algebraic.SL2HighestWeight

/-!
# Rank-one check on the actual algebraic SL₂

With upper and lower elementary matrices, the source word
n(s)=x(s)y(-s⁻¹)x(s), h(s)=n(1)⁻¹n(s) is diag(s⁻¹,s).
Its left version is the standard diagonal morphism. The first basis vector
of the natural left action is upper-fixed, with raw exponent -1 and left
exponent +1. This checks GLS3 1.12.1 against Steinberg (6.1) on actual points.
-/

@[expose] public noncomputable section
open Theory.AlgebraicGroup
namespace Triality.RestrictedWeights.SteinbergTensors.LeftWeights.RankOne
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

abbrev upper (s : k) : Variety.Point (slVariety k 2) :=
  standardSL2UpperMorphism.onPoints (kPlusPoint s)
abbrev lower (s : k) : Variety.Point (slVariety k 2) :=
  standardSL2LowerMorphism.onPoints (kPlusPoint s)

def n (s : k) : Variety.Point (slVariety k 2) := upper s * lower (-s⁻¹) * upper s

def rawWord (s : Variety.Point (KMult k)) : Variety.Point (slVariety k 2) :=
  (n (1 : k))⁻¹ * n (dPointEquiv 1 s 0 : k)

/-- The raw coroot is a regular morphism, with the inverse diagonal parameter. -/
def rawCorootMorphism : Theory.AlgebraicGroup.Morphism (KMult k) (slVariety k 2) :=
  standardSL2DiagonalMorphism.comp parameterInversion

def leftCorootMorphism : Theory.AlgebraicGroup.Morphism (KMult k) (slVariety k 2) :=
  rawCorootMorphism.comp parameterInversion

theorem diagonal_matrix (s : Variety.Point (KMult k)) :
    (slPointEquiv 2 (standardSL2DiagonalMorphism.onPoints s)).val =
      !![(dPointEquiv 1 s 0 : k), 0; 0, (dPointEquiv 1 s 0 : k)⁻¹] := by
  change typeASLDiagonalMatrix 1 s = _
  have h0 : (typeASLDiagonalEntries 1 s 0 : k) = (dPointEquiv 1 s 0 : k) :=
    congrArg Units.val (typeASLDiagonalEntries_castSucc 1 s (0 : Fin 1))
  have h1 : (typeASLDiagonalEntries 1 s 1 : k) = (dPointEquiv 1 s 0 : k)⁻¹ := by
    change (typeASLDiagonalEntries 1 s (Fin.last 1) : k) = _
    rw [typeASLDiagonalEntries_last]
    simp
  ext i j
  fin_cases i <;> fin_cases j <;> simp [typeASLDiagonalMatrix, Matrix.diagonal, h0, h1]

theorem n_matrix (s : k) (hs : s ≠ 0) :
    (slPointEquiv 2 (n s)).val = !![0, s; -s⁻¹, 0] := by
  change Matrix.transvection 0 1 s * Matrix.transvection 1 0 (-s⁻¹) *
    Matrix.transvection 0 1 s = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transvection,
      Matrix.one_apply, Matrix.single_apply, hs]

theorem rawWord_matrix (s : Variety.Point (KMult k)) :
    (slPointEquiv 2 (rawWord s)).val =
      !![(dPointEquiv 1 s 0 : k)⁻¹, 0; 0, (dPointEquiv 1 s 0 : k)] := by
  change Matrix.adjugate (slPointEquiv 2 (n (1 : k))).val *
    (slPointEquiv 2 (n (dPointEquiv 1 s 0 : k))).val = _
  rw [n_matrix 1 one_ne_zero, n_matrix _ (Units.ne_zero _)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

/-- The actual source word is the raw regular cocharacter. -/
theorem rawWord_eq_morphism (s : Variety.Point (KMult k)) :
    rawWord s = rawCorootMorphism.onPoints s := by
  apply (slPointEquiv 2).injective
  apply Subtype.ext
  change _ = (slPointEquiv 2 (standardSL2DiagonalMorphism.onPoints s⁻¹)).val
  rw [rawWord_matrix, diagonal_matrix, dPointEquiv_inverse]
  simp

/-- Inverting the raw parameter gives the standard diagonal morphism itself. -/
theorem leftCorootMorphism_eq_diagonal :
    leftCorootMorphism (k := k) = standardSL2DiagonalMorphism := by
  apply Theory.AlgebraicGroup.Morphism.ext
  funext s
  change standardSL2DiagonalMorphism.onPoints (s⁻¹)⁻¹ = _
  rw [inv_inv]
  rfl

/-- The natural two-dimensional left action, on the actual algebraic points. -/
def naturalAction : Representation k (Variety.Point (slVariety k 2)) (Fin 2 → k) where
  toFun g := Matrix.toLin' (slPointEquiv 2 g).val
  map_one' := by
    change Matrix.toLin' (1 : Matrix (Fin 2) (Fin 2) k) = 1
    exact Matrix.toLin'_one
  map_mul' g h := Matrix.toLin'_mul (slPointEquiv 2 g).val (slPointEquiv 2 h).val

def e1 : Fin 2 → k := ![1, 0]

omit [IsAlgClosed k] in
theorem e1_ne_zero : e1 (k := k) ≠ 0 := by
  intro h
  exact one_ne_zero (congrFun h 0)

omit [IsAlgClosed k] in
theorem naturalAction_finrank : Module.finrank k (Fin 2 → k) = 2 := by simp

theorem upper_fixes_e1 (u : k) : naturalAction (upper u) e1 = e1 (k := k) := by
  change (Matrix.transvection 0 1 u).mulVec ![1, 0] = ![1, 0]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.transvection, Matrix.one_apply, Matrix.single_apply]

theorem raw_exponent (s : Variety.Point (KMult k)) :
    naturalAction (rawWord s) e1 = (dPointEquiv 1 s 0 : k) ^ (-1 : ℤ) • e1 := by
  change (slPointEquiv 2 (rawWord s)).val.mulVec e1 = _
  rw [rawWord_matrix]
  ext i
  fin_cases i <;> simp [e1, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem left_exponent (s : Variety.Point (KMult k)) :
    naturalAction (leftCorootMorphism.onPoints s) e1 =
      (dPointEquiv 1 s 0 : k) ^ (1 : ℤ) • e1 := by
  rw [leftCorootMorphism_eq_diagonal]
  change (slPointEquiv 2 (standardSL2DiagonalMorphism.onPoints s)).val.mulVec e1 = _
  rw [diagonal_matrix]
  ext i
  fin_cases i <;> simp [e1, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Direct conjugation by the actual left coroot has the positive Cartan exponent. -/
theorem left_conjugation (s : Variety.Point (KMult k)) (u : k) :
    leftCorootMorphism.onPoints s * upper u * (leftCorootMorphism.onPoints s)⁻¹ =
      upper ((dPointEquiv 1 s 0 : k) ^ 2 * u) := by
  rw [leftCorootMorphism_eq_diagonal]
  have h := typeASLRootPoint_diagonal_conjugation 1 standardSL2UpperRootIndex u
    (standardSL2DiagonalMorphism.onPoints s⁻¹) (typeASLDiagonalEntries 1 s⁻¹)
    (typeASLDiagonalPoint_matrix 1 s⁻¹)
  change _ = typeASLRootPoint 1 standardSL2UpperRootIndex
    ((typeASLDiagonalEntries 1 s⁻¹ 0 : k)⁻¹ * u * (typeASLDiagonalEntries 1 s⁻¹ 1 : k)) at h
  rw [show (0 : Fin 2) = (0 : Fin 1).castSucc by rfl,
    typeASLDiagonalEntries_castSucc,
    show (1 : Fin 2) = Fin.last 1 by rfl, typeASLDiagonalEntries_last] at h
  simp only [Fin.prod_univ_one, dPointEquiv_inverse, Pi.inv_apply,
    Units.val_inv_eq_inv_val, inv_inv, map_inv] at h
  change standardSL2DiagonalMorphism.onPoints s *
    typeASLRootPoint 1 standardSL2UpperRootIndex u *
    (standardSL2DiagonalMorphism.onPoints s)⁻¹ =
      typeASLRootPoint 1 standardSL2UpperRootIndex ((dPointEquiv 1 s 0 : k) ^ 2 * u)
  rw [h]
  congr 1
  ring

/-- A nonzero actual vector witnesses both signs and the fixed upper root. -/
theorem sanity : e1 (k := k) ≠ 0 ∧
    (∀ u : k, naturalAction (upper u) e1 = e1) ∧
    (∀ s : Variety.Point (KMult k), naturalAction (rawWord s) e1 = (dPointEquiv 1 s 0 : k) ^ (-1 : ℤ) • e1) ∧
    (∀ s : Variety.Point (KMult k), naturalAction (leftCorootMorphism.onPoints s) e1 =
      (dPointEquiv 1 s 0 : k) ^ (1 : ℤ) • e1) :=
  ⟨e1_ne_zero, upper_fixes_e1, raw_exponent, left_exponent⟩

end Triality.RestrictedWeights.SteinbergTensors.LeftWeights.RankOne
