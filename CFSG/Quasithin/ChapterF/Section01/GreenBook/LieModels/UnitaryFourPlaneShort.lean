module
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourPlaneShort.Structure

/-!
# The canonical Hermitian block module of the unitary-four plane factor

The structural module proves shortness and ordinary perfectness for every
positive exponent, including the binary ground field. Here the equality
U(L₂) = O₂(L₂) and the triviality of C_U(L₂) give an actual equivalence from
U/C_U(L₂) to the additive Hermitian matrices. Together with the established
core-quotient equivalence to SL₂, this identifies the literal conjugation action
with `FiniteModel.action`; the final formula is the matrix identity A X A†.

Source: Aschbacher--Smith C.1.7, C.1.30 and F.1.12(I)(6),(II), printed pp.123,
135 and 263–264 of the combined manuscript, 1 March 2004. This completes the
shortness, Hermitian module and residual inputs to the parent plane-block
assembly, which owns the orthogonal-model comparison and ambient block result.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour
open Matrix Subgroup Theory.GroupTheory
open Representation.OrthogonalFourMinus
variable (n : ℕ) (hn : 1 ≤ n) [NeZero n]

/-- Hermitian coordinates on the actual commutator layer. -/
def L2BlockUEquiv : ChapterC.blockU (L2 n hn) ≃* Multiplicative (FiniteModel.Space n) :=
  (MulEquiv.subgroupCongr (L2_blockU_eq_twoCore n hn)).trans (L2TwoCoreEquiv n hn).symm

@[simp] theorem L2BlockUEquiv_apply (u : ChapterC.blockU (L2 n hn)) :
    L2BlockUEquiv n hn u =
      (L2TwoCoreEquiv n hn).symm ⟨u.val, (L2_blockU_eq_twoCore n hn) ▸ u.property⟩ := rfl

/-- The actual block module U/C_U(L₂), identified with the Hermitian additive group. -/
def L2BlockModuleEquiv : ChapterC.BlockModule (L2 n hn) ≃*
    Multiplicative (FiniteModel.Space n) :=
  ((QuotientGroup.quotientMulEquivOfEq (L2_blockFixed_eq_bot n hn)).trans
    QuotientGroup.quotientBot).trans (L2BlockUEquiv n hn)

@[simp] theorem L2BlockModuleEquiv_mk (u : ChapterC.blockU (L2 n hn)) :
    L2BlockModuleEquiv n hn (QuotientGroup.mk' (ChapterC.blockFixed (L2 n hn)) u) =
      L2BlockUEquiv n hn u := rfl

/-- Conjugation on the commutator layer is the existing Hermitian congruence action. -/
theorem L2BlockUEquiv_conj (g : L2 n hn) (u : ChapterC.blockU (L2 n hn)) :
    L2BlockUEquiv n hn (ChapterC.blockConjugate (L2 n hn) g u) =
      FiniteModel.multiplicativeAction n
        (L2QuotientEquivSL2 n hn (QuotientGroup.mk' (pCore 2 (L2 n hn)) g))
        (L2BlockUEquiv n hn u) :=
  L2TwoCoreEquiv_symm_conj n hn g
    ⟨u.val, (L2_blockU_eq_twoCore n hn) ▸ u.property⟩

/-- Both equivalences use the literal core quotient and fixed-subgroup quotient. -/
def L2BlockModuleModel : ChapterC.BlockModuleModel (L2 n hn)
    (FiniteModel.multiplicativeAction n) where
  quotientIso := L2QuotientEquivSL2 n hn
  moduleIso := L2BlockModuleEquiv n hn
  intertwining g u := by
    rw [L2BlockModuleEquiv_mk, L2BlockModuleEquiv_mk]
    exact L2BlockUEquiv_conj n hn g u

/-- The plane factor's canonical linear block model is the finite Hermitian action. -/
theorem L2_isLinearBlockModel : ChapterC.IsLinearBlockModel (L2 n hn) (FiniteModel.action n) :=
  ⟨FiniteModel.multiplicativeAction n, ⟨L2BlockModuleModel n hn⟩,
    FiniteModel.multiplicativeAction_apply n⟩

/-- In coordinates the block-module intertwining is literally X ↦ A X A†. -/
theorem L2BlockModuleEquiv_conj_val (g : L2 n hn) (u : ChapterC.blockU (L2 n hn)) :
    (L2BlockModuleEquiv n hn (QuotientGroup.mk' (ChapterC.blockFixed (L2 n hn))
      (ChapterC.blockConjugate (L2 n hn) g u))).toAdd.val =
      (L2QuotientEquivSL2 n hn (QuotientGroup.mk g)).val *
        (L2BlockModuleEquiv n hn (QuotientGroup.mk' (ChapterC.blockFixed (L2 n hn)) u)).toAdd.val *
          adjoint (FiniteModel.conjugation n)
            (L2QuotientEquivSL2 n hn (QuotientGroup.mk g)).val := by
  rw [L2BlockModuleEquiv_mk, L2BlockModuleEquiv_mk, L2BlockUEquiv_conj,
    FiniteModel.multiplicativeAction_apply, FiniteModel.action_apply]
  rfl

end CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour
