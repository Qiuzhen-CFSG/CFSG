module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.ModelPlacement.ExtensionBorels

/-!
# Concrete signed-three extension presentations

These presentations retain the defining exponent, the linear or quadratic
matrix field, and the actual projective or automorphism group. The mixed
presentations are literal preimages of mixed field–diagonal subgroups under
Aut → Out. The linear case uses the definition of A.3.16; identifying its
unitary graph-field fixed group with the unitary preimage remains part of
the earlier compatible extension presentation. Their root and Borel subgroups
are defined by matrices and semilinear actors, independently of any normalizer
equation.

The source classification must supply an equivalence of the whole overgroup
compatible with the embedded component. No order-three lift outside the
component is postulated for a nonsplit extension.

Source: Aschbacher–Smith, Notation A.3.16 and proof of 13.6.6, pp.51 and 927.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel.ModelPlacement
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open AutomorphismExtensionBorel
open scoped MatrixGroups Matrix

/-- The four concrete signed-three presentations in source case (iii).
The unitary parameter is the fixed-field exponent, not the matrix-field degree. -/
inductive ExtensionModel : ℕ → Type 1
  | linearDiagonal (F : Type) [Field F] [Finite F] [CharP F 2]
      {m : ℕ} (hm : 1 < m) (hF : Nat.card F = 2 ^ m) (hmod : 2 ^ m % 3 = 1) :
      ExtensionModel m
  | linearMixed (F : Type) [Field F] [Finite F]
      {m : ℕ} (hm : 1 < m) (hF : Nat.card F = 2 ^ m)
      (D : Matrix.PSL3.ExtensionBorel.MixedData F m) : ExtensionModel m
  | unitaryDiagonal (F : Type) [Field F] [Finite F]
      (J : HermitianForm 3 F) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
      {m : ℕ} (hm : 1 < m) (hF : Nat.card F = (2 ^ m) ^ 2)
      (hconj : ∀ x, J.conj x = x ^ (2 ^ m)) (hmod : 2 ^ m % 3 = 2) :
      ExtensionModel m
  | unitaryMixed (F : Type) [Field F] [Finite F]
      (J : HermitianForm 3 F) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
      {m : ℕ} (hm : 1 < m) (hF : Nat.card F = (2 ^ m) ^ 2)
      (hconj : ∀ x, J.conj x = x ^ (2 ^ m)) (hthree : 3 ∣ m) (hmod : 2 ^ m % 3 = 2)
      (σ : F ≃+* F) (hfield : orderOf σ = 3)
      (d : J.unitarySubgroup) (hdiag : ∀ i j, i ≠ j → d.val.val i j = 0)
      (houter : orderOf (QuotientGroup.mk'
        (MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J))
          (J.unitaryConj d)) = 3) : ExtensionModel m

namespace ExtensionModel

/-- The concrete component carrier. -/
def Component {m : ℕ} (M : ExtensionModel m) : Type := by
  cases M with
  | linearDiagonal F _ _ _ => exact PSL(3, F)
  | linearMixed F _ _ _ => exact PSL(3, F)
  | unitaryDiagonal F J _ _ _ _ _ => exact ↥(ProjectiveSpecialUnitaryMatrixGroup J)
  | unitaryMixed F J _ _ _ _ _ _ _ _ _ _ _ =>
    exact ↥(ProjectiveSpecialUnitaryMatrixGroup J)

instance {m : ℕ} (M : ExtensionModel m) : Group M.Component := by
  cases M <;> simp only [Component] <;> infer_instance

/-- The whole source extension. Diagonal cases use actual PGL and PGU
matrix groups; mixed cases use literal outer-quotient preimages. -/
def Carrier {m : ℕ} (M : ExtensionModel m) : Type := by
  cases M with
  | linearDiagonal F _ _ _ => exact Matrix.ProjGenLinGroup (Fin 3) F
  | linearMixed F _ _ D =>
    exact ↥(Matrix.PSL3.ExtensionBorel.mixedExtension F D.coefficient D.diagonal)
  | unitaryDiagonal F J _ _ _ _ _ => exact ↥(HermitianForm.ExtensionBorel.projectiveUnitary J)
  | unitaryMixed F J hJ _ _ _ _ _ σ _ d _ _ =>
    exact ↥(HermitianForm.ExtensionBorel.mixedPreimage J hJ σ d)

instance {m : ℕ} (M : ExtensionModel m) : Group M.Carrier := by
  cases M <;> simp only [Carrier] <;> infer_instance

/-- The literal component embedding in each whole source extension. -/
def embedding {m : ℕ} (M : ExtensionModel m) : M.Component →* M.Carrier := by
  cases M with
  | linearDiagonal F _ _ _ => exact Matrix.ProjectiveSpecialLinearGroup.toPGL
  | linearMixed F _ _ D =>
    exact innerEmbedding _
      (Matrix.PSL3.ExtensionBorel.inner_le_mixedExtension F D.coefficient D.diagonal)
  | unitaryDiagonal F J _ _ _ _ _ => exact HermitianForm.ExtensionBorel.componentInPGU J
  | unitaryMixed F J hJ _ _ _ _ _ σ _ d _ _ =>
    exact innerEmbedding _ (HermitianForm.ExtensionBorel.inner_le_mixedPreimage J hJ σ d)

/-- The model root Sylow, independently constructed from the matrices. -/
def sylow {m : ℕ} (M : ExtensionModel m) : Sylow 2 M.Component := by
  cases M with
  | linearDiagonal F hm hF _ =>
    exact Matrix.PSL3.LinearThree.unipotentSylow F (by omega) hF
  | linearMixed F hm hF _ =>
    exact Matrix.PSL3.LinearThree.unipotentSylow F (by omega) hF
  | unitaryDiagonal F J hJ hm hF hconj _ =>
    exact HermitianForm.EvenTwoRank.rootSylow J hJ (by omega) hF
      (FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 m (by omega) hF hconj)
  | unitaryMixed F J hJ hm hF hconj _ _ _ _ _ _ _ =>
    exact HermitianForm.EvenTwoRank.rootSylow J hJ (by omega) hF
      (FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 m (by omega) hF hconj)

/-- The explicit triangular or semilinear Borel, restricted to the extension. -/
def B {m : ℕ} (M : ExtensionModel m) : Subgroup M.Carrier := by
  cases M with
  | linearDiagonal F _ _ _ =>
    exact Matrix.PSL3.ExtensionBorel.pglBorel F
  | linearMixed F _ _ D =>
    exact (Matrix.PSL3.ExtensionBorel.actorBorel F).subgroupOf
      (Matrix.PSL3.ExtensionBorel.mixedExtension F D.coefficient D.diagonal)
  | unitaryDiagonal F J hJ _ _ _ _ =>
    exact HermitianForm.ExtensionBorel.pguBorel J
  | unitaryMixed F J hJ _ _ _ _ _ σ _ d _ _ =>
    exact (HermitianForm.ExtensionBorel.actorBorel J hJ).subgroupOf
      (HermitianForm.ExtensionBorel.mixedPreimage J hJ σ d)

/-- The matrix calculations identify the normalizer in the whole extension. -/
theorem normalizer_root {m : ℕ} (M : ExtensionModel m) :
    normalizer ((M.sylow : Subgroup M.Component).map M.embedding : Set M.Carrier) = M.B := by
  cases M with
  | linearDiagonal F hm hF hmod =>
    exact Matrix.PSL3.ExtensionBorel.normalizer_pgl_root F
  | linearMixed F hm hF D =>
    exact Matrix.PSL3.ExtensionBorel.normalizer_source_mixed F hm hF D
  | unitaryDiagonal F J hJ hm hF hconj hmod =>
    exact HermitianForm.ExtensionBorel.normalizer_pgu_rootSylow J hJ hm hF hconj
  | unitaryMixed F J hJ hm hF hconj hthree hmod σ hfield d hdiag houter =>
    exact HermitianForm.ExtensionBorel.source_mixed_rootSylow_normalizer
      J hJ hm hthree hmod hF hconj σ hfield d hdiag houter

end ExtensionModel
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel.ModelPlacement
