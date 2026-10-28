module

public import Theory.SpecificGroups.Triality.BinarySevenPlane.Weyl
public import Mathlib.Tactic.Group

/-!
# The six canonical A₂ curves used in the binary triality witness

Simple Weyl conjugation identifies the six roots with the diagram-fixed A₂
subsystem. Graph-field therefore squares their parameters. The full canonical
matrix comparison retains every Geck lattice coordinate, including Cartan
coordinates, and provides the link to the finite Lang certificate.
Source: the explicit binary triality nonsplit-torus construction, ATLAS p.89.
-/

@[expose] public section
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
namespace Triality.Standard.BinarySevenPlane
open ConcreteBruhat ConcreteBruhat.MatrixRealization Parabolics Parabolics.RankOneMatrices
open PositiveCoordinates.SumExchangeData
noncomputable section
local instance curveLatticeDecidableEq : DecidableEq LatticeIndex := fun a b => instDecidableEqSum a b
local notation "P" => binaryParameters 1 Nat.zero_lt_one
local notation "F" => ExtensionField P

def root (r : Fin 24) (t : F) : SplitGroup P :=
  ⟨rootCurveUnit (integralChevalleyRootOperators (b := typeDRootPairing_base 2))
    (rootEnumeration r) t, rootCurveUnit_mem_simpleSubgroup _ _⟩

lemma matrix_root (r) (t) : matrix P (root r t) = matrixCurve r t := by
  have h := RootConjugation.rootCurveUnit_matrix (rootEnumeration r) t
  ext a b
  change (rootCurveUnit (integralChevalleyRootOperators (b := typeDRootPairing_base 2))
    (rootEnumeration r) t).val (latticeEnumeration a) (latticeEnumeration b) = _
  simpa only [Equiv.symm_apply_apply, Matrix.coe_reindexRingEquiv,
    Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm] using congrFun (congrFun h a) b


lemma simple_conjugate_root (i : Fin 4) (r) (t) :
    weylWord P i 1 * root r t * (weylWord P i 1)⁻¹ = root (reflectionTable i r) t := by
  apply Subtype.ext
  exact (RootConjugation.weylWord_rootCurveUnit_conjugation P prime_two i
    (rootEnumeration r) t).trans (congrArg
      (fun q => rootCurveUnit (integralChevalleyRootOperators (b := typeDRootPairing_base 2)) q t)
      (rootEnumeration_reflectionTable i r).symm)

lemma word_conjugate_root (l) (r) (t) :
    word l * root r t * (word l)⁻¹ = root (permWord l r) t := by
  induction l with
  | nil => simp [word_nil, permWord]
  | cons i l ih =>
    rw [word_cons]
    calc
      _ = weylWord P i 1 * (word l * root r t * (word l)⁻¹) * (weylWord P i 1)⁻¹ := by group
      _ = _ := by rw [ih]; exact simple_conjugate_root i _ _

lemma root13_eq (t) : root 13 t = positiveRoot P 1 t := by
  apply Subtype.ext
  exact rootCurveUnit_simple (typeDRootPairing_baseEquiv 2 1) t

lemma graphField_root13 (t) : graphFieldAutomorphism P (root 13 t) = root 13 (t^2) := by
  rw [root13_eq, graphField_positiveRoot, root13_eq]
  rfl

lemma graphField_conjugate (l) (hl : graphFieldAutomorphism P (word l) = word l)
    (r : Fin 24) (hr : ∀ t, graphFieldAutomorphism P (root r t) = root r (t^2)) (t) :
    graphFieldAutomorphism P (root (permWord l r) t) = root (permWord l r) (t^2) := by
  rw [← word_conjugate_root l r t]
  simp only [map_mul, map_inv, hl]
  rw [hr t]
  exact word_conjugate_root l r (t^2)

lemma graphField_central : graphFieldAutomorphism P (word [1]) = word [1] := by
  rw [graphField_word]
  rfl

lemma graphField_root14 (t) : graphFieldAutomorphism P (root 14 t) = root 14 (t^2) :=
  graphField_conjugate [1] graphField_central 13 graphField_root13 t
lemma graphField_root4 (t) : graphFieldAutomorphism P (root 4 t) = root 4 (t^2) :=
  graphField_conjugate [0,2,3] graphField_arms 13 graphField_root13 t
lemma graphField_root7 (t) : graphFieldAutomorphism P (root 7 t) = root 7 (t^2) :=
  graphField_conjugate [0,2,3] graphField_arms 14 graphField_root14 t
lemma graphField_root0 (t) : graphFieldAutomorphism P (root 0 t) = root 0 (t^2) :=
  graphField_conjugate [1] graphField_central 4 graphField_root4 t
lemma graphField_root3 (t) : graphFieldAutomorphism P (root 3 t) = root 3 (t^2) :=
  graphField_conjugate [1] graphField_central 7 graphField_root7 t

end
end Triality.Standard.BinarySevenPlane
