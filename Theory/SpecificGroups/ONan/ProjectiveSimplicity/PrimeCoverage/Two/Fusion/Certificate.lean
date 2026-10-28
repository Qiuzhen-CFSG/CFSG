module

public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Two.Fusion.LinearWords
public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Two.Fusion.TreeData
public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Two.Fusion.MatrixData

/-!
# Matrix obligations for the O'Nan involution fusion trees

Word values connect the numerical tables to the actual linear lifts. A nonzero
off-diagonal entry excludes a scalar square and therefore excludes projective
order two. The tree identities avoid inverses by multiplying on the right by
the conjugating basis element. Finally seven odd-power identities provide
fusion at the roots. Every numerical condition below is an explicit proof
obligation, not an assumption about the named sporadic group.

The supplied tables are transcribed from the reproducible data in `Two/source/`.
-/

@[expose] public section
namespace ONan.Simplicity.TwoCertificate.Fusion

/-- Both numerical tables must represent the fixed linear words. -/
structure MatrixWordValues : Prop where
  basis : ∀ j, (linearBasis j : Matrix (Fin 45) (Fin 45) (ZMod 7)) = FusionData.basis j
  forms : ∀ i, (linearForm i : Matrix (Fin 45) (Fin 45) (ZMod 7)) = FusionData.form i

/-- Nonzero off-diagonal coordinates exclude all noncandidate scalar squares. -/
def MatrixSquareExclusions : Prop :=
  ∀ i : Fin 512, i ≠ 0 → (∀ t : Fin 87, vertex t ≠ i) →
    ∃ row col : Fin 45, row ≠ col ∧ (FusionData.form i ^ 2) row col ≠ 0

/-- Eighty matrix equations, one for every nonroot tree vertex. -/
def MatrixTreeProducts : Prop :=
  ∀ t : Fin 87, parent t < t →
    FusionData.form (vertex t) * FusionData.basis (label t) =
      FusionData.basis (label t) * FusionData.form (vertex (parent t))

/-- The seven ambient conjugating words, evaluated in GL. -/
def linearRootWord (r : Fin 7) : Matrix.GeneralLinearGroup (Fin 45) (ZMod 7) :=
  ambientWord linearA linearB (rootWord r)

/-- Seven full linear odd-power identities at the tree roots. -/
def MatrixRootPowers : Prop :=
  ∀ r : Fin 7,
    (FusionData.form (vertex (root r)) *
      ((linearRootWord r : Matrix (Fin 45) (Fin 45) (ZMod 7)) * matrixA *
        ((linearRootWord r)⁻¹ : Matrix.GeneralLinearGroup (Fin 45) (ZMod 7)))) ^
      (2 * rootHalfExponent r + 1) = 1

/-- Scalar exclusion suffices for candidate coverage; injectivity is not needed. -/
theorem candidates_of_matrix_certificates (hv : MatrixWordValues)
    (hs : MatrixSquareExclusions) (i : Fin 512) (hi : orderOf (indexedForm i) = 2) :
    ∃ t : Fin 87, vertex t = i := by
  classical
  by_contra hn
  have hzero : i ≠ 0 := by
    intro hz
    subst i
    rw [indexedForm_zero, orderOf_one] at hi
    omega
  obtain ⟨row, col, hne, hentry⟩ := hs i hzero (by simpa only [not_exists] using hn)
  have hpow : indexedForm i ^ 2 = 1 := by
    rw [← hi]
    exact pow_orderOf_eq_one _
  have hp : Matrix.ProjGenLinGroup.mk (linearForm i ^ 2) = 1 := by
    rw [map_pow, project_linearForm]
    exact congrArg Subtype.val hpow
  have hc := Matrix.ProjGenLinGroup.mk_eq_one.mp hp
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hc
  obtain ⟨u, hu⟩ := hc
  have he := congrArg (fun g : Matrix.GeneralLinearGroup (Fin 45) (ZMod 7) =>
    (g : Matrix (Fin 45) (Fin 45) (ZMod 7))) hu
  change Matrix.scalar (Fin 45) (u : ZMod 7) =
    (linearForm i : Matrix (Fin 45) (Fin 45) (ZMod 7)) ^ 2 at he
  rw [hv.forms i] at he
  apply hentry
  rw [← he]
  simp [Matrix.scalar_apply, hne]

/-- Linear tree products descend to conjugating identities in the fixed model. -/
theorem tree_products_of_matrix_certificates (hv : MatrixWordValues)
    (he : MatrixTreeProducts) (t : Fin 87) (ht : parent t < t) :
    indexedForm (vertex t) * generators (label t) =
      generators (label t) * indexedForm (vertex (parent t)) := by
  have h : linearForm (vertex t) * linearBasis (label t) =
      linearBasis (label t) * linearForm (vertex (parent t)) := by
    apply Units.ext
    change (linearForm (vertex t) : Matrix (Fin 45) (Fin 45) (ZMod 7)) *
        (linearBasis (label t) : Matrix (Fin 45) (Fin 45) (ZMod 7)) =
      (linearBasis (label t) : Matrix (Fin 45) (Fin 45) (ZMod 7)) *
        (linearForm (vertex (parent t)) : Matrix (Fin 45) (Fin 45) (ZMod 7))
    rw [hv.forms, hv.forms, hv.basis]
    exact he t ht
  apply Subtype.ext
  change (indexedForm (vertex t)).val * (generators (label t)).val =
    (generators (label t)).val * (indexedForm (vertex (parent t))).val
  exact (by simpa only [map_mul, project_linearForm, project_linearBasis] using
    congrArg Matrix.ProjGenLinGroup.mk h)

/-- Full linear powers yield the projective identities required by fusion. -/
theorem root_powers_of_matrix_certificates (hv : MatrixWordValues)
    (hr : MatrixRootPowers) (r : Fin 7) :
    (indexedForm (vertex (root r)) *
      (ambientWord generatorA generatorB (rootWord r) * generatorA *
        (ambientWord generatorA generatorB (rootWord r))⁻¹)) ^
      (2 * rootHalfExponent r + 1) = 1 := by
  have h : (linearForm (vertex (root r)) *
      (linearRootWord r * linearA * (linearRootWord r)⁻¹)) ^
      (2 * rootHalfExponent r + 1) = 1 := by
    apply Units.ext
    change ((linearForm (vertex (root r)) : Matrix (Fin 45) (Fin 45) (ZMod 7)) *
      ((linearRootWord r : Matrix (Fin 45) (Fin 45) (ZMod 7)) * matrixA *
        ((linearRootWord r)⁻¹ : Matrix.GeneralLinearGroup (Fin 45) (ZMod 7)))) ^
      (2 * rootHalfExponent r + 1) = 1
    rw [hv.forms]
    exact hr r
  apply Subtype.ext
  change ((indexedForm (vertex (root r))).val *
    ((ambientWord generatorA generatorB (rootWord r)).val *
      Matrix.ProjGenLinGroup.mk linearA *
      ((ambientWord generatorA generatorB (rootWord r)).val)⁻¹)) ^
        (2 * rootHalfExponent r + 1) = 1
  have hp := congrArg Matrix.ProjGenLinGroup.mk h
  simpa only [map_pow, map_mul, map_inv, map_one, linearRootWord,
    project_linearForm, project_ambientWord] using hp

end ONan.Simplicity.TwoCertificate.Fusion
