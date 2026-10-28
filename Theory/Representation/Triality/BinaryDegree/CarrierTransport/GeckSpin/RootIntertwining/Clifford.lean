module
public import Theory.Representation.Triality.BinaryDegree.CarrierTransport.GeckSpin.CliffordComparison
import all Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.RegularRoots.CliffordCurves
import Mathlib.Tactic.NoncommRing

/-!
# Clifford formulas for the full D4 adjoint comparison

The signed isotropic generators satisfy the characteristic-two Clifford
relations. Conjugation by a pinned root point is evaluated on these generators
using the explicit isotropic-pair curve. The four Cartan commutators are then
quadratic expressions; the fourth includes a scalar term.

The internal formula bridge uses `import all` only in proofs; exported types
refer to the public Clifford coordinates. These formulas are consumed by the
signed basis calculations in `RootIntertwining`.

Source: GLS3, §§1.12–1.14, especially 1.14.9(c), and §2.7.
-/

@[expose] public section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace Triality.BinaryDegree.CarrierTransport.GeckSpin.RootIntertwining
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open Triality.SimplyConnected Triality.SimplyConnected.Pinning
open CliffordAlgebra
variable (k : Type*) [Field k] [IsAlgClosed k] [CharP k 2]

def axis (b : Bool) (i : Fin 4) : QuadraticSpace k :=
  if b then (Pi.single i 1, 0) else (0, Pi.single i 1)
def gen (b : Bool) (i : Fin 4) : Clifford k := ι (quadraticForm k) (axis k b i)

lemma clifford_neg (x : Clifford k) : -x = x := by
  rw [← neg_one_smul k, CharTwo.neg_eq (1 : k), one_smul]

lemma axis_polar (b c : Bool) (i j : Fin 4) :
    (quadraticForm k).polarBilin (axis k b i) (axis k c j) =
      if b != c ∧ i = j then 1 else 0 := by
  classical
  change (hyperbolicForm 4 : QuadraticForm k (QuadraticSpace k)).polarBilin _ _ = _
  rw [hyperbolicForm_polar]
  cases b <;> cases c <;> simp [axis, Pi.single_apply, eq_comm]

lemma gen_sq (b : Bool) (i : Fin 4) : gen k b i * gen k b i = 0 := by
  rw [gen, ι_sq_scalar]
  cases b <;> simp [axis, quadraticForm]

lemma gen_swap (b c : Bool) (i j : Fin 4) :
    gen k b i * gen k c j =
      (if b != c ∧ i = j then 1 else 0) + gen k c j * gen k b i := by
  classical
  rw [gen, gen, ι_mul_ι_comm]
  rw [← QuadraticMap.polarBilin_apply_apply, axis_polar]
  simp only [sub_eq_add_neg, clifford_neg]
  split_ifs <;> simp

lemma rootBivector_gen (r : RootIndex) : rootBivector k r =
    gen k (decide (r.2.1.1 = 1)) r.1.1.1 * gen k (decide (r.2.2.1 = 1)) r.1.1.2 := by
  classical
  simp [rootBivector, rootU, rootV, rootAxis, gen, axis]

lemma conj_mul (x : Points k) (a b : Clifford k) :
    pointConjugation k x (a * b) = pointConjugation k x a * pointConjugation k x b := by
  have h : (pointEquiv k x⁻¹ : Clifford k) * (pointEquiv k x : Clifford k) = 1 := by
    change ((pointEquiv k x⁻¹ * pointEquiv k x : spinGroup (quadraticForm k)) : Clifford k) = 1
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  simp only [pointConjugation_apply]
  calc
    _ = (pointEquiv k x : Clifford k) * a * 1 * b * (pointEquiv k x⁻¹ : Clifford k) := by simp [mul_assoc]
    _ = _ := by rw [← h]; simp only [mul_assoc]

lemma conj_one (x : Points k) : pointConjugation k x 1 = 1 := by
  simp only [pointConjugation_apply, mul_one]
  change ((pointEquiv k x * pointEquiv k x⁻¹ : spinGroup (quadraticForm k)) : Clifford k) = 1
  rw [← map_mul, mul_inv_cancel, map_one]
  rfl

lemma conj_gen (r : RootIndex) (t : k) (b : Bool) (j : Fin 4) :
    pointConjugation k (rootPoint k r t) (gen k b j) =
      gen k b j + t •
        (((quadraticForm k).polarBilin (axis k (decide (r.2.2.1 = 1)) r.1.1.2) (axis k b j)) •
          gen k (decide (r.2.1.1 = 1)) r.1.1.1 -
         ((quadraticForm k).polarBilin (axis k (decide (r.2.1.1 = 1)) r.1.1.1) (axis k b j)) •
          gen k (decide (r.2.2.1 = 1)) r.1.1.2) := by
  rw [pointConjugation_apply, ← rootPoint_neg, rootPoint_clifford, rootPoint_clifford]
  simp only [rootBivector, neg_smul, ← sub_eq_add_neg, gen]
  rw [CliffordIsotropicPair.curve_conj (quadraticForm k) (rootU k r) (rootV k r)
    (rootAxis_isotropic k _ _) (rootAxis_isotropic k _ _) (rootAxes_ortho k r)]
  simp only [map_add, map_smul, map_sub]
  congr 3 <;> simp only [rootU, rootV, rootAxis, axis, decide_eq_true_eq]

lemma bivector_comm_bivector (u v w z : QuadraticSpace k) :
    (ι (quadraticForm k) u * ι (quadraticForm k) v) *
      (ι (quadraticForm k) w * ι (quadraticForm k) z) -
      (ι (quadraticForm k) w * ι (quadraticForm k) z) *
      (ι (quadraticForm k) u * ι (quadraticForm k) v) =
    ((quadraticForm k).polarBilin v w • ι (quadraticForm k) u -
      (quadraticForm k).polarBilin u w • ι (quadraticForm k) v) * ι (quadraticForm k) z +
    ι (quadraticForm k) w * ((quadraticForm k).polarBilin v z • ι (quadraticForm k) u -
      (quadraticForm k).polarBilin u z • ι (quadraticForm k) v) := by
  rw [← CliffordIsotropicPair.bivector_comm, ← CliffordIsotropicPair.bivector_comm]
  noncomm_ring

lemma gen_comm_gen (b c d e : Bool) (i j l m : Fin 4) :
    (gen k b i * gen k c j) * (gen k d l * gen k e m) -
      (gen k d l * gen k e m) * (gen k b i * gen k c j) =
    ((if c != d ∧ j = l then (1 : k) else 0) • gen k b i -
      (if b != d ∧ i = l then (1 : k) else 0) • gen k c j) * gen k e m +
    gen k d l * ((if c != e ∧ j = m then (1 : k) else 0) • gen k b i -
      (if b != e ∧ i = m then (1 : k) else 0) • gen k c j) := by
  simp only [gen, bivector_comm_bivector, axis_polar]

lemma cartan_gen (i : Fin 4) : cartanBivector k i =
    ![gen k true 0 * gen k false 0 + gen k true 1 * gen k false 1,
      gen k true 1 * gen k false 1 + gen k true 2 * gen k false 2,
      gen k true 2 * gen k false 2 + gen k true 3 * gen k false 3,
      1 + gen k true 2 * gen k false 2 + gen k true 3 * gen k false 3] i := by
  simp only [cartanBivector, rootBivector_gen, gen_comm_gen]
  fin_cases i <;>
    norm_num [negativeSimpleRoot, negativeRoot, simpleRoot,
      typeDSimpleRootIndex, sub_eq_add_neg, clifford_neg]
  all_goals simp only [gen_swap k false true]
  all_goals simp only [bne, Bool.false_beq, Bool.not_true, Bool.false_eq_true,
    Bool.not_false, and_self, ↓reduceIte]
  all_goals have h (x : Clifford k) : x + x = 0 := by simpa only [clifford_neg] using neg_add_cancel x
  all_goals abel_nf
  all_goals simp_all [two_smul, add_comm, add_left_comm, add_assoc]

lemma gen_sort (b c : Bool) (i j : Fin 4) (h : j < i) :
    gen k b i * gen k c j = gen k c j * gen k b i := by
  rw [gen_swap]
  simp [ne_of_gt h]

lemma gen_opposite (i : Fin 4) : gen k false i * gen k true i =
    1 + gen k true i * gen k false i := by
  simpa using gen_swap k false true i i

lemma clifford_two (x : Clifford k) : x + x = 0 := by
  simpa only [clifford_neg] using neg_add_cancel x

lemma conj_gen_formula (r : RootIndex) (t : k) (b : Bool) (j : Fin 4) :
    pointConjugation k (rootPoint k r t) (gen k b j) =
      gen k b j + t •
        ((if (decide (r.2.2.1 = 1)) != b ∧ r.1.1.2 = j then (1 : k) else 0) •
          gen k (decide (r.2.1.1 = 1)) r.1.1.1 +
         (if (decide (r.2.1.1 = 1)) != b ∧ r.1.1.1 = j then (1 : k) else 0) •
          gen k (decide (r.2.2.1 = 1)) r.1.1.2) := by
  rw [conj_gen, axis_polar, axis_polar, sub_eq_add_neg, clifford_neg]

end Triality.BinaryDegree.CarrierTransport.GeckSpin.RootIntertwining
