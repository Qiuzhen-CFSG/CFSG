module
public import Theory.Representation.Triality.BinaryDegree.CarrierTransport.GeckSpin.RootIntertwining.Clifford
public import Theory.SpecificGroups.Triality.LeviRankOneMatrices.Entries

/-!
# The Geck action on one comparison coordinate

The integral D4 entry formulas identify the linear and quadratic columns of
both simple-root actions. The cubic terms vanish. Applying the comparison
embedding gives a polynomial in the unchanged root parameter. These are
identities on the full Cartan-plus-root lattice, with no injectivity premise.

The signed Clifford basis calculations consume `geck_column` to recover the
literal matrix action. Source: GLS3 §§1.12–1.14, 1.14.9(c), and §2.7.
-/

@[expose] public section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace Triality.BinaryDegree.CarrierTransport.GeckSpin.RootIntertwining
open Theory.AlgebraicGroup.StandardRootSystem
open Triality.SimplyConnected Triality.SimplyConnected.Pinning
open Triality.Standard.Parabolics.RankOneMatrices
open RootPairing.SimpleGeckGroup RootPairing.IntegralGeckConstruction
open scoped Matrix
attribute [local instance] indexDecidableEq
variable (k : Type*) [Field k] [IsAlgClosed k] [CharP k 2]

lemma image_inl (i j : Fin 4) : basisImage k (flatEquiv i (.inl j)) = cartanBivector k j := by
  simp [basisImage]
lemma image_inr (i : Fin 4) (j : Fin 24) : basisImage k (flatEquiv i (.inr j)) =
    rootBivector k (orderedRoot i j) := rfl

def linearColumn (pos : Bool) (i : Fin 4) (j : FlatIndex) : Clifford k :=
  ∑ a : FlatIndex, ((if pos then eData i a j else fData i a j) : k) • basisImage k (flatEquiv i a)

def quadraticColumn (pos : Bool) (i : Fin 4) (j : FlatIndex) : Clifford k :=
  if j = .inr (if pos then 1 else 0) then basisImage k (flatEquiv i (.inr (if pos then 0 else 1))) else 0

def signedGeck (pos : Bool) (i : Fin 4) (t : k) : SplitPoints k :=
  if pos then positive (typeDRootPairing_baseEquiv 2 i) t else negative (typeDRootPairing_baseEquiv 2 i) t

def signedPoint (pos : Bool) (i : Fin 4) (t : k) : Points k :=
  if pos then positiveSimplePoint k i t else negativeSimplePoint k i t

lemma divided_one_column (pos : Bool) (i : Fin 4) (j : FlatIndex) :
    embedding k ((if pos then eDividedPower (typeDRootPairing_baseEquiv 2 i) 1
      else fDividedPower (typeDRootPairing_baseEquiv 2 i) 1).map (Int.castRingHom k) *ᵥ
        Pi.single (flatEquiv i j) 1) = linearColumn k pos i j := by
  classical
  simp only [Matrix.mulVec_single_one]
  unfold embedding
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Matrix.col_apply, Matrix.map_apply]
  rw [← (flatEquiv i).sum_comp]
  cases pos <;> simp [linearColumn, eDividedPower_one, fDividedPower_one,
    eMatrix_entry, fMatrix_entry]

lemma divided_two_column (pos : Bool) (i : Fin 4) (j : FlatIndex) :
    embedding k ((if pos then eDividedPower (typeDRootPairing_baseEquiv 2 i) 2
      else fDividedPower (typeDRootPairing_baseEquiv 2 i) 2).map (Int.castRingHom k) *ᵥ
        Pi.single (flatEquiv i j) 1) = quadraticColumn k pos i j := by
  classical
  simp only [Matrix.mulVec_single_one]
  unfold embedding
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Matrix.col_apply, Matrix.map_apply]
  rw [← (flatEquiv i).sum_comp]
  cases pos <;>
    simp only [Bool.false_eq_true, ↓reduceIte, eTwo_entry, fTwo_entry, quadraticColumn]
  all_goals split_ifs with hj
  all_goals simp [hj, ite_and, ite_smul]

lemma divided_three_zero (pos : Bool) (i : Fin 4) :
    (if pos then eDividedPower (typeDRootPairing_baseEquiv 2 i) 3
      else fDividedPower (typeDRootPairing_baseEquiv 2 i) 3) = 0 := by
  ext a b
  obtain ⟨a, rfl⟩ := (flatEquiv i).surjective a
  obtain ⟨b, rfl⟩ := (flatEquiv i).surjective b
  cases pos <;> simp [eThree_entry, fThree_entry]

lemma geck_column (pos : Bool) (i : Fin 4) (t : k) (j : FlatIndex) :
    embedding k (matrixAction k (signedGeck k pos i t) (Pi.single (flatEquiv i j) 1)) =
      basisImage k (flatEquiv i j) + t • linearColumn k pos i j +
        t ^ 2 • quadraticColumn k pos i j := by
  have h : (signedGeck k pos i t).val.val = 1 +
      t • (if pos then eDividedPower (typeDRootPairing_baseEquiv 2 i) 1
        else fDividedPower (typeDRootPairing_baseEquiv 2 i) 1).map (Int.castRingHom k) +
      t ^ 2 • (if pos then eDividedPower (typeDRootPairing_baseEquiv 2 i) 2
        else fDividedPower (typeDRootPairing_baseEquiv 2 i) 2).map (Int.castRingHom k) := by
    have he : eDividedPower (typeDRootPairing_baseEquiv 2 i) 3 = 0 := divided_three_zero true i
    have hf : fDividedPower (typeDRootPairing_baseEquiv 2 i) 3 = 0 := divided_three_zero false i
    cases pos <;> simp [signedGeck, positive, negative, positiveMatrix_formula,
      negativeMatrix_formula, he, hf]
  rw [matrixAction_apply, h]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, map_add, map_smul,
    embedding_single, one_smul, divided_one_column, divided_two_column]


lemma raisingEdge_pred (r s : Fin 24) :
    raisingEdge r s ↔ (2 ≤ s.val ∧ s.val < 18 ∧ s.val % 2 = 1) ∧ r = s - 1 := by
  simp only [raisingEdge, Fin.ext_iff, Fin.val_sub]
  have hr := r.isLt
  have hs := s.isLt
  norm_num
  omega

lemma raisingEdge_succ (r s : Fin 24) :
    raisingEdge s r ↔ (2 ≤ s.val ∧ s.val < 18 ∧ s.val % 2 = 0) ∧ r = s + 1 := by
  simp only [raisingEdge, Fin.ext_iff, Fin.val_add]
  have hr := r.isLt
  have hs := s.isLt
  norm_num
  omega

lemma linearColumn_inl (pos : Bool) (i j : Fin 4) :
    linearColumn k pos i (.inl j) =
      ((|typeDCartanMatrix 2 i j| : ℤ) : k) • basisImage k (flatEquiv i (.inr (if pos then 0 else 1))) := by
  classical
  cases pos <;>
    simp [linearColumn, eData, fData, Fintype.sum_sum_type, ite_smul]

lemma linearColumn_inr (pos : Bool) (i : Fin 4) (s : Fin 24) :
    linearColumn k pos i (.inr s) =
      (if s = (if pos then 1 else 0) then cartanBivector k i else 0) +
      (if 2 ≤ s.val ∧ s.val < 18 ∧ s.val % 2 = (if pos then 1 else 0) then
        rootBivector k (orderedRoot i (if pos then s - 1 else s + 1)) else 0) := by
  classical
  cases pos
  · simp [linearColumn, fData, Fintype.sum_sum_type, raisingEdge_succ,
      ite_smul, ite_and, Finset.sum_ite_irrel, basisImage]
  · simp [linearColumn, eData, Fintype.sum_sum_type, raisingEdge_pred,
      ite_smul, ite_and, Finset.sum_ite_irrel, basisImage]
end Triality.BinaryDegree.CarrierTransport.GeckSpin.RootIntertwining
