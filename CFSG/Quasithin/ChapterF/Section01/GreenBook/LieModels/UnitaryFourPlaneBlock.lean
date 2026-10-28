module

public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourPlaneBlock.Defs
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourPlaneShort
public import Theory.Representation.OrthogonalFourMinusHermitianEquiv
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Orthogonal

/-!
# The unitary-four plane local as a minus orthogonal block

The determinant-one plane local L₂ has elementary abelian Hermitian two-core
of order q⁴ and quotient SL₂(q²), for q = 2ⁿ and n ≥ 1. Its commutator layer
is this core, its fixed subgroup is trivial, and it is short and perfect.
The imported structural proofs establish these facts for the actual projective
factor, including q = 2, and are re-exported here.

We compose the literal Hermitian block-module equivalence with the quadratic
isometry to the existing four-dimensional minus form. The proved identification
of SL₂(q²) with the full orthogonal commutator gives the compatible quotient
equivalence. Their intertwining proves the natural Ω₄⁻(q) block assertion,
preserving quadratic values, rather than only the polarized form.

Source: Aschbacher--Smith F.1.12(I)(6), printed pp.263–264, and C.1.30,
printed p.135. The final residual application supplies the second factor's
clauses of F.1.12(II) for every two-subgroup of its plane parabolic.
-/

@[expose] public noncomputable section

namespace CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour

open Subgroup Theory.GroupTheory
open Representation.OrthogonalFourMinus
open ClassicalOrthogonal

variable (n : ℕ) (hn : 1 ≤ n) [NeZero n]

/-- The actual two-core quotient is the commutator subgroup of the full
isometry group of the existing four-dimensional minus form. -/
def L2QuotientEquivOmega : (L2 n hn ⧸ pCore 2 (L2 n hn)) ≃*
    Minus.Omega (FiniteModel.fixedField n) (Minus.Space (FiniteModel.fixedField n) 1)
      (Minus.quadraticForm (FiniteModel.fixedField n) 2) :=
  (L2QuotientEquivSL2 n hn).trans (HermitianEquiv.sl2EquivMinusOmega n)

/-- On actual cosets this equivalence is induced by restriction to the plane. -/
@[simp] theorem L2QuotientEquivOmega_mk (g : L2 n hn) :
    L2QuotientEquivOmega n hn (QuotientGroup.mk g) =
      HermitianEquiv.sl2EquivMinusOmega n (planeSL2Equiv n (L2Restriction n hn g)) := rfl

/-- Quadratic coordinates on the literal quotient U(L₂)/C_U(L₂). -/
def L2OmegaModuleEquiv : ChapterC.BlockModule (L2 n hn) ≃*
    Multiplicative (Minus.Space (FiniteModel.fixedField n) 1) :=
  (L2BlockModuleEquiv n hn).trans
    (HermitianEquiv.hermitianMinusIsometry n).toLinearEquiv.toAddEquiv.toMultiplicative

@[simp] theorem L2OmegaModuleEquiv_apply (v : ChapterC.BlockModule (L2 n hn)) :
    (L2OmegaModuleEquiv n hn v).toAdd =
      HermitianEquiv.hermitianMinusIsometry n (L2BlockModuleEquiv n hn v).toAdd := rfl

/-- The coordinate change preserves the Hermitian determinant quadratic form. -/
theorem L2OmegaModuleEquiv_quadratic (v : ChapterC.BlockModule (L2 n hn)) :
    Minus.quadraticForm (FiniteModel.fixedField n) 2 (L2OmegaModuleEquiv n hn v).toAdd =
      FiniteModel.form n (L2BlockModuleEquiv n hn v).toAdd :=
  (HermitianEquiv.hermitianMinusIsometry n).map_app _

/-- Literal conjugation is the natural action of the corresponding Omega coset. -/
theorem L2OmegaModuleEquiv_conj (g : L2 n hn) (u : ChapterC.blockU (L2 n hn)) :
    L2OmegaModuleEquiv n hn (QuotientGroup.mk' (ChapterC.blockFixed (L2 n hn))
      (ChapterC.blockConjugate (L2 n hn) g u)) =
    subgroupNaturalAction
      (Minus.Omega (FiniteModel.fixedField n) (Minus.Space (FiniteModel.fixedField n) 1)
        (Minus.quadraticForm (FiniteModel.fixedField n) 2))
      (L2QuotientEquivOmega n hn (QuotientGroup.mk' (pCore 2 (L2 n hn)) g))
      (L2OmegaModuleEquiv n hn (QuotientGroup.mk' (ChapterC.blockFixed (L2 n hn)) u)) := by
  change HermitianEquiv.hermitianMinusIsometry n
      (L2BlockModuleEquiv n hn (QuotientGroup.mk' (ChapterC.blockFixed (L2 n hn))
        (ChapterC.blockConjugate (L2 n hn) g u))).toAdd =
    subgroupNatural _ (HermitianEquiv.sl2EquivMinusOmega n
      (L2QuotientEquivSL2 n hn (QuotientGroup.mk' (pCore 2 (L2 n hn)) g)))
      (HermitianEquiv.hermitianMinusIsometry n
        (L2BlockModuleEquiv n hn (QuotientGroup.mk' (ChapterC.blockFixed (L2 n hn)) u)).toAdd)
  exact (congrArg (fun X : Multiplicative (FiniteModel.Space n) =>
    HermitianEquiv.hermitianMinusIsometry n X.toAdd)
    ((L2BlockModuleModel n hn).intertwining g u)).trans
      (HermitianEquiv.sl2EquivMinusOmega_intertwines n _ _).symm

/-- The canonical block-module quotient carries the literal minus Omega action. -/
def L2OmegaBlockModuleModel : ChapterC.BlockModuleModel (L2 n hn)
    (subgroupNaturalAction
      (Minus.Omega (FiniteModel.fixedField n) (Minus.Space (FiniteModel.fixedField n) 1)
        (Minus.quadraticForm (FiniteModel.fixedField n) 2))) where
  quotientIso := L2QuotientEquivOmega n hn
  moduleIso := L2OmegaModuleEquiv n hn
  intertwining := L2OmegaModuleEquiv_conj n hn

/-- Conjugation preserves the full quadratic form on the actual block module. -/
theorem L2OmegaModuleEquiv_quadratic_conj (g : L2 n hn) (u : ChapterC.blockU (L2 n hn)) :
    Minus.quadraticForm (FiniteModel.fixedField n) 2
      (L2OmegaModuleEquiv n hn (QuotientGroup.mk' (ChapterC.blockFixed (L2 n hn))
        (ChapterC.blockConjugate (L2 n hn) g u))).toAdd =
    Minus.quadraticForm (FiniteModel.fixedField n) 2
      (L2OmegaModuleEquiv n hn (QuotientGroup.mk' (ChapterC.blockFixed (L2 n hn)) u)).toAdd :=
  (L2OmegaBlockModuleModel n hn).orthogonal_quadratic_invariant g u

omit [NeZero n] in
/-- The second factor of the concrete U₄(q) amalgam is an Ω₄⁻(q) block,
in the literal natural-module sense of C.1.30, including q = 2. -/
theorem L2_isOmegaMinusEvenBlock : ChapterC.IsOmegaMinusEvenBlock (L2 n hn) 4 n := by
  let : NeZero n := ⟨by omega⟩
  exact ChapterC.IsOmegaMinusEvenBlock.of_model (r := 2) (by decide) hn
    (L2_isShort n hn) (FiniteModel.fixedField n) (FiniteModel.card_fixedField n)
    ⟨L2OmegaBlockModuleModel n hn⟩

omit [NeZero n] in
/-- The second-factor clauses in F.1.12(II): L₂ equals its solvable residual
and contains every two-subgroup of its plane parabolic. No q > 2 assumption
is needed for this factor. -/
theorem L2_residual_and_two_subgroup (S : Subgroup (ProjectiveGroup n hn))
    (hS : IsPGroup 2 S) (hSP : S ≤ planeParabolic n hn) :
    (solvableResidual (L2 n hn)).map (L2 n hn).subtype = L2 n hn ∧ S ≤ L2 n hn :=
  ⟨L2_solvableResidual_map n hn, two_subgroup_le_L2 n hn S hS hSP⟩

end CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour
