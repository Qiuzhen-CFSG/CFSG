module

public import CFSG.Quasithin.ClassicalModels
public import Theory.LinearAlgebra.FiniteProjectiveMatrixGroup
public import Mathlib.Algebra.IsPrimePow
public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus
public import Theory.SpecificGroups.ClassicalUnitary.StandardForm

/-!
# The classical part of the known-simple catalogue

`IsClassicalModel` supplies all six classical families, independently of the
smaller quasithin list. The previous `IsLinearUnitarySymplecticModel` interface
is retained, with a proved inclusion in the full classical contribution.
The orthogonal alternatives use the imported explicit quadratic spaces and
projective Omega carriers, including characteristic two. Split rank three,
odd rank one and minus rank two are retained, so no low-rank simple aliases
are omitted. The plus range starts at rank three; the minus range starts at
rank two and has no exceptional field-size exclusion.

The parameter restrictions follow GLS, *The Classification of the Finite
Simple Groups*, volume 3, Theorem 2.2.7, Definition 2.2.8 and §2.7 (local source
`refs/KGroup/GLS3/chapter2.tex`). They exclude `PSL₂(2)`, `PSL₂(3)`,
`PSU₃(2)` and `PSp₄(2)`. We retain the rank-one unitary and symplectic aliases
of `PSL₂(q)`, with the same two exclusions. The simple derived group
`PSp₄(2)'` is represented in the full known-simple union by `A₆`, not by the
nonsimple full group. Isomorphic entries need not be removed from a catalogue.

Every alternative uses an equivalence to an independently defined
classical carrier. For `PSU_n(q)` the coefficient field has order `q²` and its involution
is `x ↦ x^q`, exactly as in the imported classical interface and
Aschbacher–Smith, *The Classification of Quasithin Groups*, §A.2, footnote 3.
Finiteness and transport follow from the carriers and composition of
equivalences. No simplicity or classification hypothesis is used.
-/

@[expose] public section

universe u v

namespace ClassicalGroup

variable {G : Type u} {H : Type v} [Group G] [Group H] {n q : ℕ}

/-- A group with a finite projective linear model is finite. -/
theorem IsPSL.finite (h : IsPSL G n q) : Finite G := by
  rcases h with ⟨F, hF, hfin, _, ⟨e⟩⟩
  exact Finite.of_injective e e.injective

/-- A group with a finite projective unitary model is finite. -/
theorem IsPSU.finite (h : IsPSU G n q) : Finite G := by
  rcases h with ⟨F, hF, hfin, J, _, _, ⟨e⟩⟩
  exact Finite.of_injective e e.injective

/-- A group with a finite projective symplectic model is finite. -/
theorem IsPSp.finite (h : IsPSp G n q) : Finite G := by
  rcases h with ⟨F, hF, hfin, _, ⟨e⟩⟩
  exact Finite.of_injective e e.injective

private theorem exists_coefficientField (q : ℕ) (hq : IsPrimePow q) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q := by
  obtain ⟨p, e, hp, he, hq⟩ := (isPrimePow_nat_iff q).mp hq
  let : Fact p.Prime := ⟨hp⟩
  exact ⟨GaloisField p e, inferInstance, inferInstance,
    (GaloisField.card p e (Nat.ne_of_gt he)).trans hq⟩

/-- Every prime power supplies an actual finite `PSL` model. -/
theorem IsPSL.exists_model (n q : ℕ) (hq : IsPrimePow q) :
    ∃ (G : Type) (_ : Group G), Finite G ∧ IsPSL G n q := by
  obtain ⟨F, hF, hfin, hcard⟩ := exists_coefficientField q hq
  exact ⟨Matrix.ProjectiveSpecialLinearGroup (Fin n) F, inferInstance, inferInstance,
    F, hF, hfin, hcard, ⟨MulEquiv.refl _⟩⟩

/-- Every prime power supplies an actual finite `PSp` model. -/
theorem IsPSp.exists_model (r q : ℕ) (hq : IsPrimePow q) :
    ∃ (G : Type) (_ : Group G), Finite G ∧ IsPSp G r q := by
  obtain ⟨F, hF, hfin, hcard⟩ := exists_coefficientField q hq
  exact ⟨PSp r F, inferInstance, inferInstance,
    F, hF, hfin, hcard, ⟨MulEquiv.refl _⟩⟩

/-- Every prime power supplies an actual finite `POmegaPlus` model. -/
theorem IsPOmegaPlus.exists_model (r q : ℕ) (hq : IsPrimePow q) :
    ∃ (G : Type) (_ : Group G), Finite G ∧ IsPOmegaPlus G r q := by
  obtain ⟨F, hF, hfin, hcard⟩ := exists_coefficientField q hq
  exact ⟨ClassicalOrthogonal.POmegaPlus r F, inferInstance, inferInstance,
    F, hF, hfin, hcard, ⟨MulEquiv.refl _⟩⟩

/-- Every prime power supplies an actual finite `POmegaOdd` model. -/
theorem IsPOmegaOdd.exists_model (r q : ℕ) (hq : IsPrimePow q) :
    ∃ (G : Type) (_ : Group G), Finite G ∧ IsPOmegaOdd G r q := by
  obtain ⟨F, hF, hfin, hcard⟩ := exists_coefficientField q hq
  exact ⟨ClassicalOrthogonal.POmegaOdd r F, inferInstance, inferInstance,
    F, hF, hfin, hcard, ⟨MulEquiv.refl _⟩⟩

/-- The unitary family exists at every prime power, with the required
quadratic coefficient field and Frobenius conjugation actually constructed. -/
theorem IsPSU.exists_model (n q : ℕ) (hq : IsPrimePow q) :
    ∃ (G : Type) (_ : Group G), Finite G ∧ IsPSU G n q := by
  obtain ⟨F, hF, hfin, J, hcard, hconj⟩ :=
    BenderSuzuki.MatrixGroups.exists_standardHermitianForm n q hq
  exact ⟨BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J,
    inferInstance, inferInstance, F, hF, hfin, J, hcard, hconj, ⟨MulEquiv.refl _⟩⟩

end ClassicalGroup

namespace CFSG.KnownSimple

/-- The simple linear parameter range, including all positive prime powers. -/
def LinearParameters (n q : ℕ) : Prop :=
  IsPrimePow q ∧ 2 ≤ n ∧ (n = 2 → 4 ≤ q)

/-- The simple unitary parameter range. Dimension two is the `PSL₂` alias. -/
def UnitaryParameters (n q : ℕ) : Prop :=
  IsPrimePow q ∧ 2 ≤ n ∧ (n = 2 → 4 ≤ q) ∧ (n = 3 → q ≠ 2)

/-- The simple symplectic parameter range, with dimension `2r`.
Rank one is the `PSL₂` alias. -/
def SymplecticParameters (r q : ℕ) : Prop :=
  IsPrimePow q ∧ 1 ≤ r ∧ (r = 1 → 4 ≤ q) ∧ (r = 2 → q ≠ 2)

/-- The complete linear, unitary and symplectic families; an intermediate
contribution to the full known-simple class, not the whole classical list. -/
inductive IsLinearUnitarySymplecticModel (G : Type u) [Group G] : Prop
  | linear (n q : ℕ) (parameters : LinearParameters n q)
      (iso : ClassicalGroup.IsPSL G n q)
  | unitary (n q : ℕ) (parameters : UnitaryParameters n q)
      (iso : ClassicalGroup.IsPSU G n q)
  | symplectic (r q : ℕ) (parameters : SymplecticParameters r q)
      (iso : ClassicalGroup.IsPSp G r q)

variable {G : Type u} {H : Type v} [Group G] [Group H]

/-- All three families are invariant under isomorphism, across universes. -/
theorem IsLinearUnitarySymplecticModel.of_mulEquiv
    (h : IsLinearUnitarySymplecticModel G) (e : H ≃* G) :
    IsLinearUnitarySymplecticModel H := by
  cases h with
  | linear n q hp iso => exact .linear n q hp (iso.of_mulEquiv e)
  | unitary n q hp iso => exact .unitary n q hp (iso.of_mulEquiv e)
  | symplectic r q hp iso => exact .symplectic r q hp (iso.of_mulEquiv e)

/-- Finiteness is a consequence of the model witness, not a catalogue premise. -/
theorem IsLinearUnitarySymplecticModel.finite
    (h : IsLinearUnitarySymplecticModel G) : Finite G := by
  cases h with
  | linear _ _ _ iso => exact iso.finite
  | unitary _ _ _ iso => exact iso.finite
  | symplectic _ _ _ iso => exact iso.finite

theorem isLinearUnitarySymplecticModel_mulEquiv_iff (e : G ≃* H) :
    IsLinearUnitarySymplecticModel G ↔ IsLinearUnitarySymplecticModel H :=
  ⟨fun h => h.of_mulEquiv e.symm, fun h => h.of_mulEquiv e⟩

/-- The split orthogonal range, including the six-dimensional linear alias. -/
abbrev OrthogonalPlusParameters := ClassicalOrthogonal.PlusParameters

/-- The odd orthogonal range, retaining all simple low-rank aliases. -/
abbrev OrthogonalOddParameters := ClassicalOrthogonal.OddParameters

/-- The minus orthogonal range includes `PΩ₄⁻(2) ≅ PSL₂(4)`. -/
def OrthogonalMinusParameters (r q : ℕ) : Prop := IsPrimePow q ∧ 2 ≤ r

/-- The full classical contribution to the known-simple class. Each branch
requires an actual multiplicative equivalence to an independent carrier.
The exceptional derived group `PSp₄(2)' ≅ A₆` belongs to the alternating
contribution in the final union. -/
inductive IsClassicalModel (G : Type u) [Group G] : Prop
  | linear (n q : ℕ) (parameters : LinearParameters n q)
      (iso : ClassicalGroup.IsPSL G n q)
  | unitary (n q : ℕ) (parameters : UnitaryParameters n q)
      (iso : ClassicalGroup.IsPSU G n q)
  | symplectic (r q : ℕ) (parameters : SymplecticParameters r q)
      (iso : ClassicalGroup.IsPSp G r q)
  | orthogonalPlus (r q : ℕ) (parameters : OrthogonalPlusParameters r q)
      (iso : ClassicalGroup.IsPOmegaPlus G r q)
  | orthogonalOdd (r q : ℕ) (parameters : OrthogonalOddParameters r q)
      (iso : ClassicalGroup.IsPOmegaOdd G r q)
  | orthogonalMinus (r q : ℕ) (parameters : OrthogonalMinusParameters r q)
      (iso : ClassicalGroup.IsPOmegaMinus G r q)

/-- Preserve the earlier three-family contribution as a subcatalogue. -/
theorem IsLinearUnitarySymplecticModel.isClassicalModel
    (h : IsLinearUnitarySymplecticModel G) : IsClassicalModel G := by
  cases h with
  | linear n q hp iso => exact .linear n q hp iso
  | unitary n q hp iso => exact .unitary n q hp iso
  | symplectic r q hp iso => exact .symplectic r q hp iso

/-- Transport all six families, including their parameters, across universes. -/
theorem IsClassicalModel.of_mulEquiv (h : IsClassicalModel G) (e : H ≃* G) :
    IsClassicalModel H := by
  cases h with
  | linear n q hp iso => exact .linear n q hp (iso.of_mulEquiv e)
  | unitary n q hp iso => exact .unitary n q hp (iso.of_mulEquiv e)
  | symplectic r q hp iso => exact .symplectic r q hp (iso.of_mulEquiv e)
  | orthogonalPlus r q hp iso => exact .orthogonalPlus r q hp (iso.of_mulEquiv e)
  | orthogonalOdd r q hp iso => exact .orthogonalOdd r q hp (iso.of_mulEquiv e)
  | orthogonalMinus r q hp iso => exact .orthogonalMinus r q hp (iso.of_mulEquiv e)

/-- Finiteness is proved from the model, rather than assumed by the catalogue. -/
theorem IsClassicalModel.finite (h : IsClassicalModel G) : Finite G := by
  cases h with
  | linear _ _ _ iso => exact iso.finite
  | unitary _ _ _ iso => exact iso.finite
  | symplectic _ _ _ iso => exact iso.finite
  | orthogonalPlus _ _ _ iso => exact iso.finite
  | orthogonalOdd _ _ _ iso => exact iso.finite
  | orthogonalMinus _ _ _ iso => exact iso.finite

theorem isClassicalModel_mulEquiv_iff (e : G ≃* H) :
    IsClassicalModel G ↔ IsClassicalModel H :=
  ⟨fun h => h.of_mulEquiv e.symm, fun h => h.of_mulEquiv e⟩

/-- Every admissible linear parameter contributes a finite model. -/
theorem IsClassicalModel.exists_linear (n q : ℕ)
    (hp : LinearParameters n q) :
    ∃ (G : Type) (_ : Group G), Finite G ∧
      ClassicalGroup.IsPSL G n q ∧ IsClassicalModel G := by
  obtain ⟨G, hG, hfin, hmodel⟩ := ClassicalGroup.IsPSL.exists_model n q hp.1
  exact ⟨G, hG, hfin, hmodel, .linear n q hp hmodel⟩

/-- Every admissible unitary parameter contributes a finite model. -/
theorem IsClassicalModel.exists_unitary (n q : ℕ)
    (hp : UnitaryParameters n q) :
    ∃ (G : Type) (_ : Group G), Finite G ∧
      ClassicalGroup.IsPSU G n q ∧ IsClassicalModel G := by
  obtain ⟨G, hG, hfin, hmodel⟩ := ClassicalGroup.IsPSU.exists_model n q hp.1
  exact ⟨G, hG, hfin, hmodel, .unitary n q hp hmodel⟩

/-- Every admissible symplectic parameter contributes a finite model. -/
theorem IsClassicalModel.exists_symplectic (r q : ℕ)
    (hp : SymplecticParameters r q) :
    ∃ (G : Type) (_ : Group G), Finite G ∧
      ClassicalGroup.IsPSp G r q ∧ IsClassicalModel G := by
  obtain ⟨G, hG, hfin, hmodel⟩ := ClassicalGroup.IsPSp.exists_model r q hp.1
  exact ⟨G, hG, hfin, hmodel, .symplectic r q hp hmodel⟩

/-- Every admissible orthogonalPlus parameter contributes a finite model. -/
theorem IsClassicalModel.exists_orthogonalPlus (r q : ℕ)
    (hp : OrthogonalPlusParameters r q) :
    ∃ (G : Type) (_ : Group G), Finite G ∧
      ClassicalGroup.IsPOmegaPlus G r q ∧ IsClassicalModel G := by
  obtain ⟨G, hG, hfin, hmodel⟩ := ClassicalGroup.IsPOmegaPlus.exists_model r q hp.1
  exact ⟨G, hG, hfin, hmodel, .orthogonalPlus r q hp hmodel⟩

/-- Every admissible orthogonalOdd parameter contributes a finite model. -/
theorem IsClassicalModel.exists_orthogonalOdd (r q : ℕ)
    (hp : OrthogonalOddParameters r q) :
    ∃ (G : Type) (_ : Group G), Finite G ∧
      ClassicalGroup.IsPOmegaOdd G r q ∧ IsClassicalModel G := by
  obtain ⟨G, hG, hfin, hmodel⟩ := ClassicalGroup.IsPOmegaOdd.exists_model r q hp.1
  exact ⟨G, hG, hfin, hmodel, .orthogonalOdd r q hp hmodel⟩

/-- Every admissible orthogonalMinus parameter contributes a finite model. -/
theorem IsClassicalModel.exists_orthogonalMinus (r q : ℕ)
    (hp : OrthogonalMinusParameters r q) :
    ∃ (G : Type) (_ : Group G), Finite G ∧
      ClassicalGroup.IsPOmegaMinus G r q ∧ IsClassicalModel G := by
  obtain ⟨G, hG, hfin, hmodel⟩ := ClassicalGroup.IsPOmegaMinus.exists_model r q hp.1
  exact ⟨G, hG, hfin, hmodel, .orthogonalMinus r q hp hmodel⟩

end CFSG.KnownSimple
