module
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Determinant two-power subgroups of GL2

The subgroup at level m consists of the actual invertible two-by-two matrices
whose determinant has order dividing 2^m. It is the inverse image of the
corresponding roots-of-unity subgroup under determinant. These normal subgroups
form an increasing filtration, and the level-zero group is canonically SL2.

Entrywise transport by a coefficient-ring equivalence preserves the exact
membership condition because determinant commutes with coefficient maps and
the induced map on units is injective. The definitions and basic results hold
over commutative rings; no finite-field recognition theorem is assumed.

These are the source SL_m(2,q) matrix subgroups introduced before ABG
Chapter II, Section 2, Lemma 1, article p.17 (`page-018.tex`), and used in
the semilinear structure theorem II.3 Proposition 3. The unitary family is
obtained by restriction to the actual unitary subgroup.
-/

namespace Matrix.GeneralLinearGroup

/-- The actual GL2 subgroup whose determinants have order dividing two to m. -/
@[expose] public def determinantTwoPower (F : Type*) [CommRing F] (m : ℕ) :
    Subgroup (GL (Fin 2) F) :=
  (rootsOfUnity (2 ^ m) F).comap det

@[simp] public theorem mem_determinantTwoPower
    {F : Type*} [CommRing F] (m : ℕ) (A : GL (Fin 2) F) :
    A ∈ determinantTwoPower F m ↔ det A ^ (2 ^ m) = 1 := Iff.rfl

public theorem mem_determinantTwoPower_iff_orderOf_dvd
    {F : Type*} [CommRing F] (m : ℕ) (A : GL (Fin 2) F) :
    A ∈ determinantTwoPower F m ↔ orderOf (det A) ∣ 2 ^ m := by
  rw [mem_determinantTwoPower, orderOf_dvd_iff_pow_eq_one]

public instance determinantTwoPower_normal (F : Type*) [CommRing F] (m : ℕ) :
    (determinantTwoPower F m).Normal := by
  unfold determinantTwoPower
  infer_instance

public theorem determinantTwoPower_mono {F : Type*} [CommRing F]
    {m n : ℕ} (h : m ≤ n) : determinantTwoPower F m ≤ determinantTwoPower F n := by
  intro A hA
  rw [mem_determinantTwoPower_iff_orderOf_dvd] at hA ⊢
  exact hA.trans (pow_dvd_pow 2 h)

@[simp] public theorem determinantTwoPower_zero (F : Type*) [CommRing F] :
    determinantTwoPower F 0 = (det : GL (Fin 2) F →* Fˣ).ker := by
  ext A
  simp [mem_determinantTwoPower, MonoidHom.mem_ker]

/-- The level-zero source model is canonically the actual SL2 group. -/
public noncomputable def determinantTwoPowerZeroEquivSL
    (F : Type*) [CommRing F] :
    determinantTwoPower F 0 ≃* Matrix.SpecialLinearGroup (Fin 2) F where
  toFun A := ⟨A.val.val, by
    have h : det A.val = 1 := by simpa using A.property
    exact congrArg Units.val h⟩
  invFun A := ⟨Matrix.SpecialLinearGroup.toGL A, by
    simp only [mem_determinantTwoPower, pow_zero, pow_one,
      Matrix.SpecialLinearGroup.coeToGL_det]⟩
  left_inv A := Subtype.ext (Units.ext rfl)
  right_inv A := rfl
  map_mul' A B := rfl

/-- The canonical level-zero equivalence preserves the underlying matrix. -/
public theorem determinantTwoPowerZeroEquivSL_toGL
    (F : Type*) [CommRing F] (A : determinantTwoPower F 0) :
    Matrix.SpecialLinearGroup.toGL (determinantTwoPowerZeroEquivSL F A) = A.val := by
  apply Units.ext
  rfl

public theorem determinantTwoPower_mem_map_iff
    {F K : Type*} [CommRing F] [CommRing K] (e : F ≃+* K)
    (m : ℕ) (A : GL (Fin 2) F) :
    map e.toRingHom A ∈ determinantTwoPower K m ↔ A ∈ determinantTwoPower F m := by
  rw [mem_determinantTwoPower, mem_determinantTwoPower, GeneralLinearGroup.map_det]
  change (Units.map e.toRingHom.toMonoidHom (det A)) ^ (2 ^ m) = 1 ↔ _
  rw [← map_pow]
  constructor
  · intro h
    apply (Units.map_injective (f := e.toRingHom.toMonoidHom) e.injective)
    exact h.trans (map_one _).symm
  · intro h
    rw [h, map_one]

end Matrix.GeneralLinearGroup
