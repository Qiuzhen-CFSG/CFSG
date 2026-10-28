module
public import Theory.Representation.Triality.BinaryDegree.CarrierTransport.GeckSpin.CliffordComparison
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.Diagram.PointRealization.Clifford
import all Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.RegularRoots.CliffordCurves
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.PointGeneration.RootTable
import Mathlib.Tactic
/-!
# Independence of the 28 concrete Geck Clifford coordinates

The full sixteen-dimensional Fock action detects the root bivectors and the
four Cartan commutators. A root coefficient is recovered from one off-diagonal
matrix entry. Four diagonal entries recover the Cartan coefficients; the
constant term of the fourth Cartan vector is retained in characteristic two.

The small recovery identity is checked over `ZMod 2` and transported through
its canonical map to the coefficient field. The coordinate enumeration is
proved equivalent to the literal Cartan-plus-root index, and applying the dual
functionals to the defining sum proves injectivity of `embedding`.

The proof-only `import all` bridge unfolds the existing Clifford root vectors;
no private definition appears in an exported statement. This supplies `hι` in
`GeckSpin.exists_finite_comparison_of_clifford`.
Source: GLS3, §§1.12–1.14, especially 1.14.9(c), and §2.7.
-/

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open Triality.SimplyConnected Triality.SimplyConnected.Pinning
open Triality.SimplyConnected.Pinning.PointGeneration
open Triality.SimplyConnected.Diagram.HalfSpin
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
noncomputable section
namespace Triality.BinaryDegree.CarrierTransport.GeckSpin.Faithfulness
variable (k : Type*) [Field k] [CharP k 2]

def rootFock (r : RootIndex) (w : Fock k) (s : Mask) : k :=
  if s r.1.1.1 = decide (r.2.1.1 = 1) ∧ s r.1.1.2 = decide (r.2.2.1 = 1)
  then w (flip (flip s r.1.1.1) r.1.1.2) else 0

lemma axis_fock (i : Fin 4) (t : ℝ) (w : Fock k) (s : Mask) :
    vectorAction k (rootAxis k i t) w s =
      if s i = decide (t = 1) then w (Diagram.HalfSpin.flip s i) else 0 := by
  classical
  change (∑ j : Fin 4, (if s j then (rootAxis k i t).1 j else (rootAxis k i t).2 j) *
    w (Diagram.HalfSpin.flip s j)) = _
  rw [Finset.sum_eq_single i]
  · by_cases ht : t = 1 <;> cases hs : s i <;> simp [rootAxis, ht, hs]
  · intro j _ hji
    by_cases ht : t = 1 <;> cases hs : s j <;> simp [rootAxis, ht, Pi.single_apply, hji]
  · simp

lemma root_fock (r : RootIndex) (w : Fock k) (s : Mask) :
    cliffordAction k (rootBivector k r) w s = rootFock k r w s := by
  classical
  have hij : r.1.1.1 ≠ r.1.1.2 := r.1.2.ne
  simp only [rootBivector, map_mul, cliffordAction_ι, Module.End.mul_apply,
    rootU, rootV, axis_fock]
  simp only [rootFock, Diagram.HalfSpin.flip, Function.update_of_ne hij.symm]
  split_ifs <;> simp_all

def cartanCoeff (i : Fin 4) (s : Mask) : ZMod 2 :=
  ![(if s 0 then 1 else 0) + (if s 1 then 1 else 0),
    (if s 1 then 1 else 0) + (if s 2 then 1 else 0),
    (if s 2 then 1 else 0) + (if s 3 then 1 else 0),
    1 + (if s 2 then 1 else 0) + (if s 3 then 1 else 0)] i

def binaryCast : ZMod 2 →+* k := ZMod.castHom (dvd_refl 2) k

lemma flip_apply (s : Mask) (i j : Fin 4) :
    Diagram.HalfSpin.flip s i j = if j = i then !(s i) else s j := by
  simp [Diagram.HalfSpin.flip, Function.update_apply]

lemma flip_pair_twice (s : Mask) (i j : Fin 4) :
    Diagram.HalfSpin.flip (Diagram.HalfSpin.flip
      (Diagram.HalfSpin.flip (Diagram.HalfSpin.flip s i) j) i) j = s := by
  funext p
  by_cases hi : p = i <;> by_cases hj : p = j <;>
    simp_all [flip_apply]

lemma cartan_fock (i : Fin 4) (w : Fock k) (s : Mask) :
    cliffordAction k (cartanBivector k i) w s = binaryCast k (cartanCoeff i s) * w s := by
  simp only [cartanBivector, map_sub, map_mul, LinearMap.sub_apply, Pi.sub_apply,
    Module.End.mul_apply, root_fock]
  fin_cases i
  · cases hi : s 0 <;> cases hj : s 1
    all_goals
      norm_num [root_fock, rootFock, simpleRoot, negativeSimpleRoot, negativeRoot,
        typeDSimpleRootIndex, flip_apply, flip_pair_twice,
        hi, hj, cartanCoeff, map_add, map_one, map_zero, CharTwo.neg_eq,
        CharTwo.add_self_eq_zero,
        show s (⟨2, by decide⟩ : Fin 4) = s 2 from rfl,
        show s (⟨3, by decide⟩ : Fin 4) = s 3 from rfl]
  · cases hi : s 1 <;> cases hj : s 2
    all_goals
      norm_num [root_fock, rootFock, simpleRoot, negativeSimpleRoot, negativeRoot,
        typeDSimpleRootIndex, flip_apply, flip_pair_twice,
        hi, hj, cartanCoeff, map_add, map_one, map_zero, CharTwo.neg_eq,
        CharTwo.add_self_eq_zero,
        show s (⟨2, by decide⟩ : Fin 4) = s 2 from rfl,
        show s (⟨3, by decide⟩ : Fin 4) = s 3 from rfl]
  · cases hi : s 2 <;> cases hj : s 3
    all_goals
      norm_num [root_fock, rootFock, simpleRoot, negativeSimpleRoot, negativeRoot,
        typeDSimpleRootIndex, flip_apply, flip_pair_twice,
        hi, hj, cartanCoeff, map_add, map_one, map_zero, CharTwo.neg_eq,
        CharTwo.add_self_eq_zero,
        show s (⟨2, by decide⟩ : Fin 4) = s 2 from rfl,
        show s (⟨3, by decide⟩ : Fin 4) = s 3 from rfl]
  · cases hi : s 2 <;> cases hj : s 3
    all_goals
      norm_num [root_fock, rootFock, simpleRoot, negativeSimpleRoot, negativeRoot,
        typeDSimpleRootIndex, flip_apply, flip_pair_twice,
        hi, hj, cartanCoeff, map_add, map_one, map_zero, CharTwo.neg_eq,
        CharTwo.add_self_eq_zero,
        show s (⟨2, by decide⟩ : Fin 4) = s 2 from rfl,
        show s (⟨3, by decide⟩ : Fin 4) = s 3 from rfl]


abbrev Flat := Fin 4 ⊕ Fin 24

def axes : Fin 24 → Fin 4 × Fin 4 :=
  ![(0,1),(0,1),(0,1),(0,1),(0,2),(0,2),(0,2),(0,2),
    (0,3),(0,3),(0,3),(0,3),(1,2),(1,2),(1,2),(1,2),
    (1,3),(1,3),(1,3),(1,3),(2,3),(2,3),(2,3),(2,3)]
def signs (r : Fin 24) : Bool × Bool := (decide (2 ≤ r.val % 4), decide (r.val % 2 = 1))
def rowMask (r : Fin 24) : Mask :=
  fun i => if i = (axes r).1 then (signs r).1 else if i = (axes r).2 then (signs r).2 else false
def colMask (r : Fin 24) : Mask :=
  Diagram.HalfSpin.flip (Diagram.HalfSpin.flip (rowMask r) (axes r).1) (axes r).2

def coeff : Flat → Mask → Mask → ZMod 2
  | .inl i, s, t => if s = t then cartanCoeff i s else 0
  | .inr r, s, t =>
    if s (axes r).1 = (signs r).1 ∧ s (axes r).2 = (signs r).2 ∧
      Diagram.HalfSpin.flip (Diagram.HalfSpin.flip s (axes r).1) (axes r).2 = t then 1 else 0

def diagonalMask : Fin 4 → Mask :=
  ![![false,false,false,false], ![true,false,false,false],
    ![false,true,false,false], ![false,false,false,true]]

def recover (i : Flat) (M : Mask → Mask → ZMod 2) : ZMod 2 :=
  match i with
  | .inl i => ![M (diagonalMask 1) (diagonalMask 1) + M (diagonalMask 0) (diagonalMask 0),
    M (diagonalMask 2) (diagonalMask 2) + M (diagonalMask 1) (diagonalMask 1),
    M (diagonalMask 3) (diagonalMask 3), M (diagonalMask 0) (diagonalMask 0)] i
  | .inr r => M (rowMask r) (colMask r)

lemma recovery (i : Flat) : ∀ j : Flat,
    recover i (coeff j) = if i = j then 1 else 0 := by
  rcases i with i | i
  all_goals fin_cases i <;> decide

def rootNumber (r : RootIndex) : ℕ :=
  (if r.1.1.1 = 0 then r.1.1.2.val - 1
    else if r.1.1.1 = 1 then r.1.1.2.val + 1 else 5) * 4 +
    (if r.2.1.1 = 1 then 2 else 0) + (if r.2.2.1 = 1 then 1 else 0)

lemma rootNumber_rootAt (r : Fin 24) : rootNumber (rootAt r) = r.val := by
  fin_cases r <;> norm_num [rootAt, rootNumber, Fin.ext_iff]

def rootEquiv : Fin 24 ≃ RootIndex := Equiv.ofBijective rootAt
  ⟨fun a b h => Fin.ext (by simpa only [rootNumber_rootAt] using congrArg rootNumber h),
    rootAt_surjective⟩

def indexEquiv : Flat ≃ Index := Equiv.sumCongr (typeDRootPairing_baseEquiv 2) rootEquiv

lemma root_axes (r : Fin 24) : (rootAt r).1.1 = axes r := by
  fin_cases r <;> rfl

lemma root_signs (r : Fin 24) :
    (decide ((rootAt r).2.1.1 = 1), decide ((rootAt r).2.2.1 = 1)) = signs r := by
  fin_cases r <;> norm_num [rootAt, signs]

lemma fock_coeff (j : Flat) (s t : Mask) :
    cliffordAction k (basisImage k (indexEquiv j)) (Pi.single t 1) s =
      binaryCast k (coeff j s t) := by
  cases j with
  | inl i =>
    simp only [indexEquiv, Equiv.sumCongr_apply, basisImage, Equiv.symm_apply_apply,
      cartan_fock, Pi.single_apply, coeff]
    by_cases h : s = t <;> simp [h, cartan_fock, Pi.single_apply]
  | inr r =>
    change cliffordAction k (rootBivector k (rootAt r)) (Pi.single t 1) s = _
    have ha := congrArg Prod.fst (root_axes r)
    have hb := congrArg Prod.snd (root_axes r)
    have hc := congrArg Prod.fst (root_signs r)
    have hd := congrArg Prod.snd (root_signs r)
    dsimp only at ha hb hc hd
    simp only [root_fock, rootFock, ha, hb, hc, hd, coeff, Pi.single_apply]
    split_ifs <;> simp_all

def evaluation (s t : Mask) : Module.End k (Fock k) →ₗ[k] k where
  toFun T := T (Pi.single t 1) s
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def detector : Flat → Module.End k (Fock k) →ₗ[k] k
  | .inl i => ![evaluation k (diagonalMask 1) (diagonalMask 1) +
      evaluation k (diagonalMask 0) (diagonalMask 0),
    evaluation k (diagonalMask 2) (diagonalMask 2) + evaluation k (diagonalMask 1) (diagonalMask 1),
    evaluation k (diagonalMask 3) (diagonalMask 3),
    evaluation k (diagonalMask 0) (diagonalMask 0)] i
  | .inr r => evaluation k (rowMask r) (colMask r)

lemma detector_basis (i j : Flat) :
    detector k i (cliffordAction k (basisImage k (indexEquiv j))) =
      if i = j then 1 else 0 := by
  have hh := congrArg (binaryCast k) (recovery i j)
  have hc : detector k i (cliffordAction k (basisImage k (indexEquiv j))) =
      binaryCast k (recover i (coeff j)) := by
    cases i with
    | inl i => fin_cases i <;> simp [detector, evaluation, recover, fock_coeff, map_add]
    | inr r => exact fock_coeff k j _ _
  rw [hc, hh]
  split_ifs <;> simp

lemma embedding_injective_aux : Function.Injective (GeckSpin.embedding k) := by
  classical
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  have hh (i : Flat) : v (indexEquiv i) = 0 := by
    have ht := congrArg (fun c : Clifford k => detector k i (cliffordAction k c)) hv
    change detector k i (cliffordAction k (∑ j, v j • basisImage k j)) = _ at ht
    rw [← Equiv.sum_comp indexEquiv] at ht
    simpa only [map_sum, map_smul, detector_basis, smul_eq_mul,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      map_zero] using ht
  funext j
  obtain ⟨i,rfl⟩ := indexEquiv.surjective j
  exact hh i

end Triality.BinaryDegree.CarrierTransport.GeckSpin.Faithfulness

namespace Triality.BinaryDegree.CarrierTransport.GeckSpin
variable (k : Type*) [Field k] [CharP k 2]

/-- The concrete Cartan-plus-root Clifford embedding is injective in characteristic two. -/
public theorem embedding_injective : Function.Injective (embedding k) :=
  Faithfulness.embedding_injective_aux k

/-- The four Cartan commutators and twenty-four root bivectors are independent. -/
public theorem basisImage_linearIndependent : LinearIndependent k (basisImage k) := by
  rw [linearIndependent_iff_injective_fintypeLinearCombination]
  exact embedding_injective k

end Triality.BinaryDegree.CarrierTransport.GeckSpin
