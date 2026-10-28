module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPlaneRadical.Structure
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourPlaneRadical.Action
public import Theory.Representation.OrthogonalFourMinusFirstCohomology.FiniteModel.Geometry
public import Theory.Representation.OrthogonalFourMinusFirstCohomology.FiniteModel.Faithfulness

/-!
# The actual two-core, quotient and action of the unitary-four plane local

The block diagonal Levi section makes restriction surjective. The entire
Hermitian kernel is therefore the two-core, in both the matrix and projective
local groups. Its order is (2^n)^4 and it is elementary abelian, including n=1.
The first isomorphism theorem identifies the actual two-core quotient with
SL₂ over the quadratic extension, using the established field identification
between the two Galois-field index conventions.

The coordinate equivalences intertwine arbitrary local conjugation with the
literal Hermitian matrix action of the corresponding quotient coset. They also
commute with projectivization. The quotient is identified with the faithful
Hermitian action image from `FiniteModel.Faithfulness`, acting on the existing
four-dimensional minus-type quadratic space of `FiniteModel.Geometry`.
In particular, exactly the two-core acts trivially on the two-core.

Source: the radical, quotient and natural-module calculations for the Ω₄⁻
block in Aschbacher--Smith F.1.12(I)(6), printed pp.263–264. These discharge the
core and action identifications for the plane-block consumer. Shortness and
residuals, and hence the full source block assertion, have separate owners.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour
open Matrix
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPlaneRadical
open Representation.OrthogonalFourMinus
variable (n : ℕ) (hn : 1 ≤ n)

/-- The actual block diagonal section in the matrix local. -/
def L2MatrixLevi : SpecialLinearGroup (Fin 2) (MatrixField n) →* L2Matrix n hn :=
  levi (MatrixField n) (fieldConj n) (fieldConj_involutive n hn)

@[simp] theorem L2MatrixRestriction_levi (A : SpecialLinearGroup (Fin 2) (MatrixField n)) :
    L2MatrixRestriction n hn (L2MatrixLevi n hn A) = A :=
  factorRestriction_levi (MatrixField n) (fieldConj n) (fieldConj_involutive n hn) A

/-- The same section after actual projectivization. -/
def L2Levi : SpecialLinearGroup (Fin 2) (MatrixField n) →* L2 n hn :=
  (L2ProjectIso n hn).toMonoidHom.comp (L2MatrixLevi n hn)

@[simp] theorem L2Restriction_levi (A : SpecialLinearGroup (Fin 2) (MatrixField n)) :
    L2Restriction n hn (L2Levi n hn A) = A := by
  change L2Restriction n hn (L2ProjectIso n hn (L2MatrixLevi n hn A)) = A
  rw [L2Restriction_project, L2MatrixRestriction_levi]

theorem L2MatrixRestriction_surjective : Function.Surjective (L2MatrixRestriction n hn) :=
  fun A => ⟨L2MatrixLevi n hn A, L2MatrixRestriction_levi n hn A⟩

theorem L2Restriction_surjective : Function.Surjective (L2Restriction n hn) :=
  fun A => ⟨L2Levi n hn A, L2Restriction_levi n hn A⟩

/-- Recognition of the matrix kernel as the actual two-core. -/
theorem L2MatrixRadical_eq_twoCore : L2MatrixRadical n hn = pCore 2 (L2Matrix n hn) :=
  radical_eq_twoCore (MatrixField n) (fieldConj n) (fieldConj_involutive n hn)

/-- Recognition of the projective kernel, with no extra quotient premise. -/
theorem L2Radical_eq_twoCore : L2Radical n hn = pCore 2 (L2 n hn) := by
  have hm : (L2MatrixRadical n hn).map (L2ProjectIso n hn).toMonoidHom = L2Radical n hn := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      change L2Restriction n hn (L2ProjectIso n hn x) = 1
      rw [L2Restriction_project]
      exact hx
    · intro hg
      exact ⟨(L2ProjectIso n hn).symm g, hg, (L2ProjectIso n hn).apply_symm_apply g⟩
  rw [← hm, L2MatrixRadical_eq_twoCore, pCore_map_iso]

instance L2MatrixTwoCore_elementaryAbelian : IsElementaryAbelian 2 (pCore 2 (L2Matrix n hn)) := by
  rw [← L2MatrixRadical_eq_twoCore]
  infer_instance

instance L2TwoCore_elementaryAbelian : IsElementaryAbelian 2 (pCore 2 (L2 n hn)) := by
  rw [← L2Radical_eq_twoCore]
  infer_instance

theorem L2MatrixTwoCore_card : Nat.card (pCore 2 (L2Matrix n hn)) = (2 ^ n) ^ 4 := by
  rw [← L2MatrixRadical_eq_twoCore, L2MatrixRadical_card]

theorem L2TwoCore_card : Nat.card (pCore 2 (L2 n hn)) = (2 ^ n) ^ 4 := by
  rw [← L2Radical_eq_twoCore, L2Radical_card]

/-- Hermitian coordinates of the actual matrix two-core. -/
def L2MatrixTwoCoreEquiv [NeZero n] :
    Multiplicative (FiniteModel.Space n) ≃* pCore 2 (L2Matrix n hn) :=
  (L2MatrixRadicalEquiv n hn).trans (MulEquiv.subgroupCongr (L2MatrixRadical_eq_twoCore n hn))

/-- Hermitian coordinates of the actual projective two-core. -/
def L2TwoCoreEquiv [NeZero n] :
    Multiplicative (FiniteModel.Space n) ≃* pCore 2 (L2 n hn) :=
  (L2RadicalEquiv n hn).trans (MulEquiv.subgroupCongr (L2Radical_eq_twoCore n hn))

@[simp] theorem L2MatrixTwoCoreEquiv_val [NeZero n] (X : Multiplicative (FiniteModel.Space n)) :
    (L2MatrixTwoCoreEquiv n hn X).val = (L2MatrixRadicalEquiv n hn X).val := rfl

@[simp] theorem L2TwoCoreEquiv_val [NeZero n] (X : Multiplicative (FiniteModel.Space n)) :
    (L2TwoCoreEquiv n hn X).val = (L2RadicalEquiv n hn X).val := rfl

@[simp] theorem L2TwoCoreEquiv_project [NeZero n] (X : Multiplicative (FiniteModel.Space n)) :
    (L2TwoCoreEquiv n hn X).val = L2ProjectIso n hn (L2MatrixTwoCoreEquiv n hn X).val := rfl

/-- Matrix quotient identified with SL₂ over the finite Hermitian model's field. -/
def L2MatrixQuotientEquivSL2 :
    (L2Matrix n hn ⧸ pCore 2 (L2Matrix n hn)) ≃*
      SpecialLinearGroup (Fin 2) (FiniteModel.Field n) :=
  (quotientEquivSL2 (MatrixField n) (fieldConj n) (fieldConj_involutive n hn)).trans
    (planeSL2Equiv n)

/-- Projective quotient identified using its literal restriction homomorphism. -/
def L2QuotientEquivSL2 :
    (L2 n hn ⧸ pCore 2 (L2 n hn)) ≃*
      SpecialLinearGroup (Fin 2) (FiniteModel.Field n) :=
  ((QuotientGroup.quotientMulEquivOfEq (L2Radical_eq_twoCore n hn).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (L2Restriction n hn)
      (L2Restriction_surjective n hn))).trans (planeSL2Equiv n)

@[simp] theorem L2MatrixQuotientEquivSL2_mk (g : L2Matrix n hn) :
    L2MatrixQuotientEquivSL2 n hn (QuotientGroup.mk g) =
      planeSL2Equiv n (L2MatrixRestriction n hn g) := rfl

@[simp] theorem L2QuotientEquivSL2_mk (g : L2 n hn) :
    L2QuotientEquivSL2 n hn (QuotientGroup.mk g) =
      planeSL2Equiv n (L2Restriction n hn g) := rfl

/-- Projectivization also identifies the actual two-core quotients. -/
def L2QuotientProjectIso :
    (L2Matrix n hn ⧸ pCore 2 (L2Matrix n hn)) ≃* (L2 n hn ⧸ pCore 2 (L2 n hn)) :=
  QuotientGroup.congr _ _ (L2ProjectIso n hn) (pCore_map_iso 2 (L2ProjectIso n hn))

@[simp] theorem L2QuotientProjectIso_mk (g : L2Matrix n hn) :
    L2QuotientProjectIso n hn (QuotientGroup.mk g) = QuotientGroup.mk (L2ProjectIso n hn g) := rfl

/-- Both quotient identifications commute with the given projective map. -/
theorem L2QuotientEquivSL2_project (q : L2Matrix n hn ⧸ pCore 2 (L2Matrix n hn)) :
    L2QuotientEquivSL2 n hn (L2QuotientProjectIso n hn q) = L2MatrixQuotientEquivSL2 n hn q := by
  induction q using QuotientGroup.induction_on with
  | H g => simp

/-- Conjugation by every matrix local element is the action of its quotient coset. -/
theorem L2MatrixTwoCoreEquiv_conj [NeZero n] (g : L2Matrix n hn)
    (X : Multiplicative (FiniteModel.Space n)) :
    MulAut.conjNormal g (L2MatrixTwoCoreEquiv n hn X) =
      L2MatrixTwoCoreEquiv n hn (Multiplicative.ofAdd (FiniteModel.action n
        (L2MatrixQuotientEquivSL2 n hn (QuotientGroup.mk g)) X.toAdd)) := by
  apply Subtype.ext
  exact congrArg (fun u : L2MatrixRadical n hn => u.val) (L2MatrixRadicalEquiv_conj n hn g X)

/-- The same quotient-action formula in the actual projective group. -/
theorem L2TwoCoreEquiv_conj [NeZero n] (g : L2 n hn)
    (X : Multiplicative (FiniteModel.Space n)) :
    MulAut.conjNormal g (L2TwoCoreEquiv n hn X) =
      L2TwoCoreEquiv n hn (Multiplicative.ofAdd (FiniteModel.action n
        (L2QuotientEquivSL2 n hn (QuotientGroup.mk g)) X.toAdd)) := by
  apply Subtype.ext
  exact congrArg (fun u : L2Radical n hn => u.val) (L2RadicalEquiv_conj n hn g X)

theorem L2MatrixTwoCoreEquiv_symm_conj [NeZero n] (g : L2Matrix n hn)
    (u : pCore 2 (L2Matrix n hn)) :
    (L2MatrixTwoCoreEquiv n hn).symm (MulAut.conjNormal g u) =
      Multiplicative.ofAdd (FiniteModel.action n
        (L2MatrixQuotientEquivSL2 n hn (QuotientGroup.mk g))
        ((L2MatrixTwoCoreEquiv n hn).symm u).toAdd) := by
  obtain ⟨X, rfl⟩ := (L2MatrixTwoCoreEquiv n hn).surjective u
  rw [L2MatrixTwoCoreEquiv_conj, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]

theorem L2TwoCoreEquiv_symm_conj [NeZero n] (g : L2 n hn) (u : pCore 2 (L2 n hn)) :
    (L2TwoCoreEquiv n hn).symm (MulAut.conjNormal g u) =
      Multiplicative.ofAdd (FiniteModel.action n
        (L2QuotientEquivSL2 n hn (QuotientGroup.mk g)) ((L2TwoCoreEquiv n hn).symm u).toAdd) := by
  obtain ⟨X, rfl⟩ := (L2TwoCoreEquiv n hn).surjective u
  rw [L2TwoCoreEquiv_conj, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]

/-- Literal Hermitian matrix coordinates of conjugation in the matrix two-core. -/
theorem L2MatrixTwoCoreEquiv_symm_conj_val [NeZero n] (g : L2Matrix n hn)
    (u : pCore 2 (L2Matrix n hn)) :
    ((L2MatrixTwoCoreEquiv n hn).symm (MulAut.conjNormal g u)).toAdd.val =
      (L2MatrixQuotientEquivSL2 n hn (QuotientGroup.mk g)).val *
        ((L2MatrixTwoCoreEquiv n hn).symm u).toAdd.val *
          adjoint (FiniteModel.conjugation n)
            (L2MatrixQuotientEquivSL2 n hn (QuotientGroup.mk g)).val := by
  rw [L2MatrixTwoCoreEquiv_symm_conj]
  rfl

/-- Literal Hermitian matrix coordinates of conjugation in the projective two-core. -/
theorem L2TwoCoreEquiv_symm_conj_val [NeZero n] (g : L2 n hn) (u : pCore 2 (L2 n hn)) :
    ((L2TwoCoreEquiv n hn).symm (MulAut.conjNormal g u)).toAdd.val =
      (L2QuotientEquivSL2 n hn (QuotientGroup.mk g)).val *
        ((L2TwoCoreEquiv n hn).symm u).toAdd.val *
          adjoint (FiniteModel.conjugation n)
            (L2QuotientEquivSL2 n hn (QuotientGroup.mk g)).val := by
  rw [L2TwoCoreEquiv_symm_conj]
  rfl

/-- The actual quotient is the faithful, form-preserving Hermitian action image. -/
def L2QuotientEquivActionImage [NeZero n] :
    (L2 n hn ⧸ pCore 2 (L2 n hn)) ≃* FiniteModel.actionImage n :=
  (L2QuotientEquivSL2 n hn).trans (FiniteModel.sl2EquivActionImage n)

/-- This image acts on the native two-core by literal local conjugation. -/
theorem L2QuotientEquivActionImage_conj [NeZero n] (g : L2 n hn) (u : pCore 2 (L2 n hn)) :
    ((L2TwoCoreEquiv n hn).symm (MulAut.conjNormal g u)).toAdd =
      L2QuotientEquivActionImage n hn (QuotientGroup.mk g) •
        ((L2TwoCoreEquiv n hn).symm u).toAdd := by
  rw [L2TwoCoreEquiv_symm_conj]
  exact (FiniteModel.sl2EquivActionImage_smul n _ _).symm

/-- The determinant form of minus type is preserved by actual local conjugation. -/
theorem L2TwoCore_conj_preserves_form [NeZero n] (g : L2 n hn) (u : pCore 2 (L2 n hn)) :
    FiniteModel.form n ((L2TwoCoreEquiv n hn).symm (MulAut.conjNormal g u)).toAdd =
      FiniteModel.form n ((L2TwoCoreEquiv n hn).symm u).toAdd := by
  rw [L2QuotientEquivActionImage_conj]
  exact FiniteModel.actionImage_preserves_form n _ _

/-- Exactly the two-core acts trivially by conjugation on the two-core. -/
theorem L2TwoCore_conjugation_ker :
    (MulAut.conjNormal : L2 n hn →* MulAut (pCore 2 (L2 n hn))).ker = pCore 2 (L2 n hn) := by
  let : NeZero n := ⟨by omega⟩
  ext g
  change MulAut.conjNormal g = 1 ↔ g ∈ pCore 2 (L2 n hn)
  conv_rhs => rw [← L2Radical_eq_twoCore]
  change MulAut.conjNormal g = 1 ↔ L2Restriction n hn g = 1
  constructor
  · intro hg
    have ha : FiniteModel.action n (planeSL2Equiv n (L2Restriction n hn g)) = 1 := by
      apply LinearMap.ext
      intro X
      have he := L2TwoCoreEquiv_conj n hn g (Multiplicative.ofAdd X)
      rw [hg] at he
      have hx := (L2TwoCoreEquiv n hn).injective he
      exact (congrArg Multiplicative.toAdd hx).symm
    have he := (FiniteModel.action_injective n) (ha.trans (map_one _).symm)
    exact (planeSL2Equiv n).injective (he.trans (map_one _).symm)
  · intro hg
    apply MulEquiv.ext
    intro u
    obtain ⟨X, rfl⟩ := (L2TwoCoreEquiv n hn).surjective u
    rw [L2TwoCoreEquiv_conj, L2QuotientEquivSL2_mk, hg, map_one, map_one]
    rfl

end CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour
