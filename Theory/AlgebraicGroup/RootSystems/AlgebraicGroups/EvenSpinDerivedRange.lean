module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.EvenOrthogonalSpinAction
public import Theory.AlgebraicGroup.RootSystems.SplitCliffordDicksonParity
public import Theory.AlgebraicGroup.RootSystems.SplitOrthogonalLipschitzGeneration
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic

/-!
# The derived subgroup of a split even orthogonal group

For a split finite-dimensional quadratic form of hyperbolic rank at least four,
this module identifies the image of the Clifford Spin action with the abstract
commutator subgroup of the full quadratic isometry group.  The statement is
characteristic-free: in particular, it neither describes the image by a
determinant nor assumes that two is invertible.

The proof represents every isometry as a product of the characteristic-free
conjugation symmetries from `SplitQuadraticConjugationGeneration`.  Algebraic
closure makes all anisotropic symmetry lines conjugate.  Normally one symmetry
in the sum or difference of two equal-norm vectors supplies the conjugacy.  If
both are isotropic, their equations force characteristic two; a common
isotropic partner in the split model then supplies a two-symmetry conjugacy.
Consequently every pair of symmetries is a commutator, so every even symmetry
word lies in the derived subgroup.

For the reverse comparison, anisotropic vectors are normalized to Clifford
units of norm one.  Even symmetry words therefore lift explicitly to
`spinGroup Q`.  The split Clifford Dickson-parity theorem shows that any
symmetry factorization of a Spin image has even length.  Conversely an
arbitrary group commutator lifts from the even word obtained by adjoining the
two reversed factorizations.  These inputs are the split Cartan--Dieudonne and
Clifford parity constructions developed in the preceding root-system modules.
-/

open CliffordAlgebra
open scoped commutatorElement

universe u

namespace Theory.AlgebraicGroup

variable {k V : Type u} [Field k] [IsAlgClosed k]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable {Q : QuadraticForm k V}

/-- A vector on which the quadratic form is nonzero. -/
public abbrev AnisotropicVector (Q : QuadraticForm k V) :=
  {a : V // Q a ≠ 0}

/-- The quadratic-isometry point defined by conjugation symmetry in an
anisotropic vector. -/
@[expose] public noncomputable def symmetryPoint (a : AnisotropicVector Q) :
    quadraticIsometrySubgroup Q :=
  ⟨(conjugationSymmetry Q a.1 a.2).toLinearEquiv,
    (mem_quadraticIsometrySubgroup Q _).2
      (fun v => (conjugationSymmetry Q a.1 a.2).map_app v)⟩

omit [IsAlgClosed k] [FiniteDimensional k V] in
public lemma symmetryPoint_apply (a : AnisotropicVector Q) (v : V) :
    (symmetryPoint a).1 v = conjugationSymmetry Q a.1 a.2 v :=
  rfl

omit [IsAlgClosed k] [FiniteDimensional k V] in
private lemma symmetryPoint_sq (a : AnisotropicVector Q) :
    symmetryPoint a * symmetryPoint a = 1 := by
  apply Subtype.ext
  ext v
  change conjugationSymmetry Q a.1 a.2
      (conjugationSymmetry Q a.1 a.2 v) = v
  exact conjugationSymmetry_involutive Q a.1 a.2 v

omit [IsAlgClosed k] [FiniteDimensional k V] in
private lemma symmetryPoint_inv (a : AnisotropicVector Q) :
    (symmetryPoint a)⁻¹ = symmetryPoint a := by
  exact (eq_inv_iff_mul_eq_one.mpr (symmetryPoint_sq a)).symm

/-- The quadratic-isometry point represented by a word of conjugation
symmetries. -/
@[expose] public noncomputable def symmetryProductPoint
    (as : List (AnisotropicVector Q)) : quadraticIsometrySubgroup Q :=
  (as.map symmetryPoint).prod

omit [IsAlgClosed k] [FiniteDimensional k V] in
public lemma symmetryProductPoint_apply
    (as : List (AnisotropicVector Q)) (v : V) :
    (symmetryProductPoint as).1 v =
      as.foldr (fun a w => conjugationSymmetry Q a.1 a.2 w) v := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      change conjugationSymmetry Q a.1 a.2 ((symmetryProductPoint as).1 v) = _
      rw [ih]
      rfl

private lemma exists_symmetryFactorization
    (s : SplitQuadraticForm Q) (g : quadraticIsometrySubgroup Q) :
    ∃ as : List (AnisotropicVector Q), symmetryProductPoint as = g := by
  obtain ⟨as, has⟩ := split_conjugation_factorization s g.1
    ((mem_quadraticIsometrySubgroup Q g.1).1 g.2)
  refine ⟨as, ?_⟩
  apply Subtype.ext
  ext v
  rw [symmetryProductPoint_apply]
  simpa only [conjugationSymmetry_apply] using (has v).symm

private noncomputable def normalizingScalar
    (a : AnisotropicVector Q) : k :=
  Classical.choose (IsAlgClosed.exists_eq_mul_self (-(Q a.1)⁻¹))

omit [FiniteDimensional k V] in
private lemma normalizingScalar_spec (a : AnisotropicVector Q) :
    -(Q a.1)⁻¹ = normalizingScalar a * normalizingScalar a :=
  Classical.choose_spec (IsAlgClosed.exists_eq_mul_self (-(Q a.1)⁻¹))

omit [FiniteDimensional k V] in
private lemma normalizingScalar_ne_zero (a : AnisotropicVector Q) :
    normalizingScalar a ≠ 0 := by
  intro h
  have hzero : -(Q a.1)⁻¹ = 0 := by rw [normalizingScalar_spec, h, zero_mul]
  exact (neg_ne_zero.mpr (inv_ne_zero a.2)) hzero

private noncomputable def normalizedVector (a : AnisotropicVector Q) : V :=
  normalizingScalar a • a.1

omit [FiniteDimensional k V] in
private lemma normalizedVector_norm (a : AnisotropicVector Q) :
    Q (normalizedVector a) = -1 := by
  rw [normalizedVector, QuadraticMap.map_smul]
  simp only [smul_eq_mul]
  rw [← normalizingScalar_spec a, neg_mul, inv_mul_cancel₀ a.2]

omit [FiniteDimensional k V] in
private lemma normalizedVector_ne_zero (a : AnisotropicVector Q) :
    Q (normalizedVector a) ≠ 0 := by
  rw [normalizedVector_norm]
  exact neg_ne_zero.mpr one_ne_zero

private noncomputable def normalizedUnit (a : AnisotropicVector Q) :
    (CliffordAlgebra Q)ˣ where
  val := CliffordAlgebra.ι Q (normalizedVector a)
  inv := -CliffordAlgebra.ι Q (normalizedVector a)
  val_inv := by simp [CliffordAlgebra.ι_sq_scalar, normalizedVector_norm]
  inv_val := by simp [CliffordAlgebra.ι_sq_scalar, normalizedVector_norm]

omit [FiniteDimensional k V] in
@[simp] private lemma normalizedUnit_val (a : AnisotropicVector Q) :
    (normalizedUnit a : CliffordAlgebra Q) =
      CliffordAlgebra.ι Q (normalizedVector a) :=
  rfl

omit [FiniteDimensional k V] in
private lemma normalizedVector_mem_pinGroup (a : AnisotropicVector Q) :
    CliffordAlgebra.ι Q (normalizedVector a) ∈ pinGroup Q := by
  rw [pinGroup.mem_iff]
  refine ⟨?_, ?_⟩
  · refine ⟨normalizedUnit a, ?_, rfl⟩
    exact Subgroup.subset_closure ⟨normalizedVector a, normalizedUnit_val a⟩
  · exact ⟨by simp [normalizedVector_norm], by simp [normalizedVector_norm]⟩

omit [FiniteDimensional k V] in
private lemma normalizedUnits_prod_mem_pinGroup
    (as : List (AnisotropicVector Q)) :
    ((as.map normalizedUnit).prod : CliffordAlgebra Q) ∈ pinGroup Q := by
  induction as with
  | nil => simp
  | cons a as ih =>
      simp only [List.map_cons, List.prod_cons, Units.val_mul, normalizedUnit_val]
      exact mul_mem (normalizedVector_mem_pinGroup a) ih

omit [FiniteDimensional k V] in
private lemma normalizedUnits_prod_mem_evenOdd
    (as : List (AnisotropicVector Q)) :
    ((as.map normalizedUnit).prod : CliffordAlgebra Q) ∈
      CliffordAlgebra.evenOdd Q (as.length : ZMod 2) := by
  induction as with
  | nil => simpa using
      (SetLike.one_mem_graded (A := CliffordAlgebra.evenOdd Q))
  | cons a as ih =>
      simp only [List.map_cons, List.prod_cons, Units.val_mul,
        normalizedUnit_val, List.length_cons, Nat.cast_add, Nat.cast_one]
      simpa [add_comm] using SetLike.mul_mem_graded
        (CliffordAlgebra.ι_mem_evenOdd_one Q (normalizedVector a)) ih

omit [FiniteDimensional k V] in
private lemma normalizedUnit_inv_mem_evenOdd_one (a : AnisotropicVector Q) :
    (↑((normalizedUnit a)⁻¹) : CliffordAlgebra Q) ∈
      CliffordAlgebra.evenOdd Q 1 := by
  change -CliffordAlgebra.ι Q (normalizedVector a) ∈
    CliffordAlgebra.evenOdd Q 1
  exact Submodule.neg_mem _
    (CliffordAlgebra.ι_mem_evenOdd_one Q (normalizedVector a))

omit [FiniteDimensional k V] in
private lemma normalizedUnits_prod_inv_mem_evenOdd
    (as : List (AnisotropicVector Q)) :
    (↑((as.map normalizedUnit).prod⁻¹) : CliffordAlgebra Q) ∈
      CliffordAlgebra.evenOdd Q (as.length : ZMod 2) := by
  induction as with
  | nil => simpa using
      (SetLike.one_mem_graded (A := CliffordAlgebra.evenOdd Q))
  | cons a as ih =>
      simp only [List.map_cons, List.prod_cons, mul_inv_rev, Units.val_mul,
        List.length_cons, Nat.cast_add, Nat.cast_one]
      simpa [add_comm] using SetLike.mul_mem_graded ih
        (normalizedUnit_inv_mem_evenOdd_one a)

private noncomputable def evenSymmetrySpinLift
    (as : List (AnisotropicVector Q)) (has : Even as.length) : spinGroup Q := by
  let p := (as.map normalizedUnit).prod
  refine ⟨(p : CliffordAlgebra Q), ?_⟩
  rw [spinGroup.mem_iff]
  refine ⟨normalizedUnits_prod_mem_pinGroup as, ?_⟩
  have hgrade := normalizedUnits_prod_mem_evenOdd as
  have hcast : (as.length : ZMod 2) = 0 := has.natCast_zmod_two
  rwa [hcast] at hgrade

omit [IsAlgClosed k] [FiniteDimensional k V] in
private lemma conjugationSymmetry_smul (a : AnisotropicVector Q)
    (c : k) (hc : c ≠ 0) (v : V) :
    conjugationSymmetry Q (c • a.1)
        (by simp [QuadraticMap.map_smul, hc, a.2]) v =
      conjugationSymmetry Q a.1 a.2 v := by
  rw [conjugationSymmetry_apply, conjugationSymmetry_apply]
  simp only [QuadraticMap.map_smul, QuadraticMap.polar_smul_left, smul_smul]
  apply congrArg (fun z : k => z • a.1 - v)
  field_simp [hc, a.2]
  ring

omit [FiniteDimensional k V] in
private lemma normalizedUnit_conjugation
    (a : AnisotropicVector Q) (v : V) :
    (normalizedUnit a : CliffordAlgebra Q) * CliffordAlgebra.ι Q v *
        (↑((normalizedUnit a)⁻¹) : CliffordAlgebra Q) =
      CliffordAlgebra.ι Q (conjugationSymmetry Q a.1 a.2 v) := by
  change CliffordAlgebra.ι Q (normalizedVector a) * CliffordAlgebra.ι Q v *
      (-CliffordAlgebra.ι Q (normalizedVector a)) = _
  let _ : Invertible (Q (normalizedVector a)) :=
    invertibleOfNonzero (normalizedVector_ne_zero a)
  let _ : Invertible (CliffordAlgebra.ι Q (normalizedVector a)) :=
    CliffordAlgebra.invertibleιOfInvertible Q (normalizedVector a)
  have hinv : -CliffordAlgebra.ι Q (normalizedVector a) =
      ⅟(CliffordAlgebra.ι Q (normalizedVector a)) := by
    rw [CliffordAlgebra.invOf_ι, invOf_eq_inv, normalizedVector_norm]
    simp
  rw [hinv, CliffordAlgebra.ι_mul_ι_mul_invOf_ι]
  apply congrArg (CliffordAlgebra.ι Q)
  rw [invOf_eq_inv]
  simpa only [normalizedVector, conjugationSymmetry_apply] using
    conjugationSymmetry_smul a (normalizingScalar a)
      (normalizingScalar_ne_zero a) v

omit [FiniteDimensional k V] in
private lemma normalizedUnits_prod_conjugation
    (as : List (AnisotropicVector Q)) (v : V) :
    CliffordAlgebra.ι Q
        (as.foldr (fun a w => conjugationSymmetry Q a.1 a.2 w) v) =
      ((as.map normalizedUnit).prod : CliffordAlgebra Q) *
        CliffordAlgebra.ι Q v *
          (↑((as.map normalizedUnit).prod⁻¹) : CliffordAlgebra Q) := by
  induction as with
  | nil => simp
  | cons a as ih =>
      rw [List.foldr_cons, ← normalizedUnit_conjugation, ih]
      simp only [List.map_cons, List.prod_cons, Units.val_mul, mul_inv_rev]
      simp [mul_assoc]

private lemma evenSymmetrySpinLift_action
    (s : SplitQuadraticForm Q) (as : List (AnisotropicVector Q))
    (has : Even as.length) :
    cliffordSpinActionOfSplit Q s (evenSymmetrySpinLift as has) =
      symmetryProductPoint as := by
  apply Subtype.ext
  ext v
  apply CliffordAlgebra.ι_injective_of_actionForm Q s.actionForm
  rw [cliffordSpinActionOfSplit_spec]
  let p := (as.map normalizedUnit).prod
  have hp : spinGroup.toUnits (evenSymmetrySpinLift as has) = p := by
    apply Units.ext
    change ((as.map normalizedUnit).prod : CliffordAlgebra Q) = _
    rfl
  have hpval : (evenSymmetrySpinLift as has : CliffordAlgebra Q) =
      (p : CliffordAlgebra Q) := by
    change ((as.map normalizedUnit).prod : CliffordAlgebra Q) = _
    rfl
  rw [hp, hpval, symmetryProductPoint_apply]
  exact (normalizedUnits_prod_conjugation as v).symm

private lemma symmetryFactorization_even_of_spinAction
    (s : SplitQuadraticForm Q) (hs : 0 < s.rank) (x : spinGroup Q)
    (as : List (AnisotropicVector Q))
    (hfac : symmetryProductPoint as = cliffordSpinActionOfSplit Q s x) :
    Even as.length := by
  let _ : Nontrivial (CliffordAlgebra Q) :=
    s.cliffordToExterior.symm.injective.nontrivial
  let a : (CliffordAlgebra Q)ˣ := spinGroup.toUnits x
  let b : (CliffordAlgebra Q)ˣ := (as.map normalizedUnit).prod
  have haEven : (a : CliffordAlgebra Q) ∈ CliffordAlgebra.even Q := by
    exact spinGroup.mem_even x.2
  have hbPin : (b : CliffordAlgebra Q) ∈ pinGroup Q := by
    exact normalizedUnits_prod_mem_pinGroup as
  have hbLip : b ∈ lipschitzGroup Q :=
    pinGroup.units_mem_lipschitzGroup hbPin
  have hconj (v : V) :
      (a : CliffordAlgebra Q) * CliffordAlgebra.ι Q v * ↑(a⁻¹) =
        (b : CliffordAlgebra Q) * CliffordAlgebra.ι Q v * ↑(b⁻¹) := by
    calc
      (a : CliffordAlgebra Q) * CliffordAlgebra.ι Q v * ↑(a⁻¹) =
          CliffordAlgebra.ι Q ((cliffordSpinActionOfSplit Q s x).1 v) :=
        (cliffordSpinActionOfSplit_spec Q s x v).symm
      _ = CliffordAlgebra.ι Q ((symmetryProductPoint as).1 v) := by rw [hfac]
      _ = (b : CliffordAlgebra Q) * CliffordAlgebra.ι Q v * ↑(b⁻¹) := by
        rw [symmetryProductPoint_apply]
        exact normalizedUnits_prod_conjugation as v
  have hquotEven : (↑(a * b⁻¹) : CliffordAlgebra Q) ∈
      CliffordAlgebra.even Q :=
    CliffordAlgebra.mul_inv_mem_even_of_mem_even_of_lipschitzGroup
      s hs haEven hbLip hconj
  have hbInvGrade : (↑(b⁻¹) : CliffordAlgebra Q) ∈
      CliffordAlgebra.evenOdd Q (as.length : ZMod 2) :=
    normalizedUnits_prod_inv_mem_evenOdd as
  have hquotGrade : (↑(a * b⁻¹) : CliffordAlgebra Q) ∈
      CliffordAlgebra.evenOdd Q (as.length : ZMod 2) := by
    simpa using SetLike.mul_mem_graded haEven hbInvGrade
  by_contra hasEven
  have hasOdd : Odd as.length := Nat.not_even_iff_odd.mp hasEven
  have hcast : (as.length : ZMod 2) = 1 := hasOdd.natCast_zmod_two
  rw [hcast] at hquotGrade
  have hbot : (↑(a * b⁻¹) : CliffordAlgebra Q) ∈
      (⊥ : Submodule k (CliffordAlgebra Q)) :=
    (CliffordAlgebra.evenOdd_isCompl Q).disjoint.le_bot
      ⟨hquotEven, hquotGrade⟩
  have hzero : (↑(a * b⁻¹) : CliffordAlgebra Q) = 0 := by
    simpa only [Submodule.mem_bot] using hbot
  exact Units.ne_zero (a * b⁻¹) hzero

omit [IsAlgClosed k] [FiniteDimensional k V] in
private lemma isometry_polar {W : Type u} [AddCommGroup W] [Module k W]
    {R : QuadraticForm k W} (g : Q.IsometryEquiv R) (a b : V) :
    QuadraticMap.polar R (g a) (g b) = QuadraticMap.polar Q a b := by
  simp only [QuadraticMap.polar, ← map_add, g.map_app]

private lemma exists_isotropic_common_partner (s : SplitQuadraticForm Q)
    (a b : V) (ha : Q a ≠ 0) (hb : Q b ≠ 0) :
    ∃ z : V, Q z = 0 ∧ QuadraticMap.polar Q a z ≠ 0 ∧
      QuadraticMap.polar Q b z ≠ 0 := by
  classical
  let A := s.isometry a
  let B := s.isometry b
  have hA2 : A.2 ≠ 0 := by
    intro h
    apply ha
    calc
      Q a = hyperbolicForm s.rank A := (s.isometry.map_app a).symm
      _ = 0 := by rw [hyperbolicForm_apply]; simp [h]
  have hB2 : B.2 ≠ 0 := by
    intro h
    apply hb
    calc
      Q b = hyperbolicForm s.rank B := (s.isometry.map_app b).symm
      _ = 0 := by rw [hyperbolicForm_apply]; simp [h]
  obtain ⟨i, hi⟩ : ∃ i, A.2 i ≠ 0 := by
    simpa only [Pi.zero_apply] using Function.ne_iff.mp hA2
  by_cases hBi : B.2 i ≠ 0
  · let Z : HyperbolicSpace k s.rank := (Pi.single i 1, 0)
    let z : V := s.isometry.symm Z
    refine ⟨z, ?_, ?_, ?_⟩
    · rw [← s.isometry.map_app]
      simp [z, Z, hyperbolicForm_apply]
    · rw [← isometry_polar s.isometry]
      rw [← QuadraticMap.polarBilin_apply_apply]
      rw [show s.isometry a = A by rfl, show s.isometry z = Z by simp [z]]
      change (hyperbolicForm s.rank).polarBilin A Z ≠ 0
      rw [hyperbolicForm_polar]
      simpa [Z, Pi.single_apply] using hi
    · rw [← isometry_polar s.isometry]
      rw [← QuadraticMap.polarBilin_apply_apply]
      rw [show s.isometry b = B by rfl, show s.isometry z = Z by simp [z]]
      change (hyperbolicForm s.rank).polarBilin B Z ≠ 0
      rw [hyperbolicForm_polar]
      simpa [Z, Pi.single_apply] using hBi
  · obtain ⟨j, hj⟩ : ∃ j, B.2 j ≠ 0 := by
      simpa only [Pi.zero_apply] using Function.ne_iff.mp hB2
    obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset
      ({0, -A.2 i * (A.2 j)⁻¹} : Finset k)
    have ht0 : t ≠ 0 := by
      intro ht0
      apply ht
      simp [ht0]
    have hAt : A.2 i + t * A.2 j ≠ 0 := by
      by_cases hAj : A.2 j = 0
      · simpa [hAj] using hi
      · intro hzero
        have h : t * A.2 j = -A.2 i := by
          linear_combination hzero
        apply ht
        simp only [Finset.mem_insert, Finset.mem_singleton]
        right
        calc
          t = (t * A.2 j) * (A.2 j)⁻¹ := by field_simp [hAj]
          _ = -A.2 i * (A.2 j)⁻¹ := by rw [h]
    let U : Fin s.rank → k := Pi.single i 1 + t • Pi.single j 1
    let Z : HyperbolicSpace k s.rank := (U, 0)
    let z : V := s.isometry.symm Z
    refine ⟨z, ?_, ?_, ?_⟩
    · rw [← s.isometry.map_app]
      simp [z, Z, hyperbolicForm_apply]
    · rw [← isometry_polar s.isometry]
      rw [← QuadraticMap.polarBilin_apply_apply]
      rw [show s.isometry a = A by rfl, show s.isometry z = Z by simp [z]]
      change (hyperbolicForm s.rank).polarBilin A Z ≠ 0
      rw [hyperbolicForm_polar]
      simpa [Z, U, Pi.single_apply,
        Finset.sum_add_distrib, add_mul] using hAt
    · rw [← isometry_polar s.isometry]
      rw [← QuadraticMap.polarBilin_apply_apply]
      rw [show s.isometry b = B by rfl, show s.isometry z = Z by simp [z]]
      have hBt : B.2 i + t * B.2 j ≠ 0 := by
        rw [show B.2 i = 0 from not_ne_iff.mp hBi, zero_add]
        exact mul_ne_zero ht0 hj
      change (hyperbolicForm s.rank).polarBilin B Z ≠ 0
      rw [hyperbolicForm_polar]
      simpa [Z, U, Pi.single_apply,
        Finset.sum_add_distrib, add_mul] using hBt

omit [IsAlgClosed k] [FiniteDimensional k V] in
private lemma conjugationSymmetry_maps_eq_neg
    (a b : V) (heq : Q a = Q b)
    (hdiff : Q (a - b) ≠ 0) :
    conjugationSymmetry Q (a - b) hdiff a = -b := by
  have hqdiff :
      Q (a - b) = Q a + Q b - QuadraticMap.polar Q a b := by
    rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg,
      QuadraticMap.polar_neg_right]
    ring
  have hpolar : QuadraticMap.polar Q (a - b) a = Q (a - b) := by
    rw [QuadraticMap.polar_sub_left, QuadraticMap.polar_self, hqdiff, heq]
    simp only [nsmul_eq_mul, Nat.cast_ofNat]
    rw [QuadraticMap.polar_comm]
    ring
  rw [conjugationSymmetry_apply, hpolar, inv_mul_cancel₀ hdiff, one_smul]
  abel

private lemma exists_isometry_maps_anisotropic_line
    (s : SplitQuadraticForm Q) (a b : AnisotropicVector Q) :
    ∃ g : quadraticIsometrySubgroup Q, ∃ c : k,
      c ≠ 0 ∧ g.1 a.1 = c • b.1 := by
  classical
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_eq_mul_self (Q a.1 * (Q b.1)⁻¹)
  have hc0 : c ≠ 0 := by
    intro hc0
    have hzero : Q a.1 * (Q b.1)⁻¹ = 0 := by rw [hc, hc0, zero_mul]
    exact (mul_ne_zero a.2 (inv_ne_zero b.2)) hzero
  let b' : V := c • b.1
  have hb' : Q b' ≠ 0 := by
    simp only [b', QuadraticMap.map_smul]
    exact mul_ne_zero (mul_ne_zero hc0 hc0) b.2
  have heq : Q a.1 = Q b' := by
    simp only [b', QuadraticMap.map_smul]
    simp only [smul_eq_mul]
    rw [← hc]
    field_simp [b.2]
  by_cases hdiff : Q (a.1 - b') ≠ 0
  · let d : AnisotropicVector Q := ⟨a.1 - b', hdiff⟩
    refine ⟨symmetryPoint d, -c, neg_ne_zero.mpr hc0, ?_⟩
    rw [symmetryPoint_apply]
    change conjugationSymmetry Q (a.1 - b') hdiff a.1 = _
    rw [conjugationSymmetry_maps_eq_neg a.1 b' heq hdiff]
    simp [b']
  · have hdiff0 : Q (a.1 - b') = 0 := not_ne_iff.mp hdiff
    by_cases hsum : Q (a.1 + b') ≠ 0
    · let d : AnisotropicVector Q := ⟨a.1 + b', hsum⟩
      refine ⟨symmetryPoint d, c, hc0, ?_⟩
      rw [symmetryPoint_apply]
      have hmap := conjugationSymmetry_maps_eq_neg
        (Q := Q) a.1 (-b') (by simpa using heq) (by simpa using hsum)
      simpa [b'] using hmap
    · have hsum0 : Q (a.1 + b') = 0 := not_ne_iff.mp hsum
      have hdiffEq :
          Q a.1 + Q b' - QuadraticMap.polar Q a.1 b' = 0 := by
        simpa [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg,
          QuadraticMap.polar_neg_right] using hdiff0
      have hsumEq :
          Q a.1 + Q b' + QuadraticMap.polar Q a.1 b' = 0 := by
        simpa [QuadraticMap.map_add Q] using hsum0
      have hfour : (4 : k) * Q a.1 = 0 := by
        rw [← heq] at hdiffEq hsumEq
        linear_combination hdiffEq + hsumEq
      have hfourScalar : (4 : k) = 0 :=
        (mul_eq_zero.mp hfour).resolve_right a.2
      have htwo : (2 : k) = 0 := by
        apply mul_self_eq_zero.mp
        calc
          (2 : k) * 2 = 4 := by norm_num
          _ = 0 := hfourScalar
      have hab : QuadraticMap.polar Q a.1 b' = 0 := by
        rw [← heq] at hdiffEq
        linear_combination Q a.1 * htwo - hdiffEq
      obtain ⟨z, hz, haz, hbz⟩ :=
        exists_isotropic_common_partner s a.1 b' a.2 hb'
      obtain ⟨r, hr⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset k)
      have hr0 : r ≠ 0 := by
        intro hr0
        apply hr
        simp [hr0]
      have hr1 : r ≠ 1 := by
        intro hr1
        apply hr
        simp [hr1]
      have hrSq : 1 - r * r ≠ 0 := by
        intro hrs
        have hrs' : (r - 1) * (r - 1) = 0 := by
          linear_combination -hrs + (1 - r) * htwo
        exact hr1 (sub_eq_zero.mp (mul_self_eq_zero.mp hrs'))
      let d : k := (1 - r * r) * Q a.1 * (r * QuadraticMap.polar Q a.1 z)⁻¹
      have hd : d ≠ 0 := by
        exact mul_ne_zero (mul_ne_zero hrSq a.2)
          (inv_ne_zero (mul_ne_zero hr0 haz))
      let w : V := r • a.1 + d • z
      have hwq : Q w = Q a.1 := by
        simp only [w, QuadraticMap.map_add Q, QuadraticMap.map_smul,
          QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right,
          hz, smul_eq_mul, mul_zero, add_zero]
        simp only [d]
        field_simp [hr0, haz]
        ring
      have haa : QuadraticMap.polar Q a.1 a.1 = 0 := by
        rw [QuadraticMap.polar_self]
        simp only [nsmul_eq_mul, Nat.cast_ofNat, htwo, zero_mul]
      have hbb : QuadraticMap.polar Q b' a.1 = 0 := by
        rw [QuadraticMap.polar_comm]
        exact hab
      have haw : QuadraticMap.polar Q a.1 w ≠ 0 := by
        simp only [w]
        rw [QuadraticMap.polar_add_right,
          QuadraticMap.polar_smul_right, QuadraticMap.polar_smul_right, haa]
        simpa using mul_ne_zero hd haz
      have hbw : QuadraticMap.polar Q b' w ≠ 0 := by
        simp only [w]
        rw [QuadraticMap.polar_add_right,
          QuadraticMap.polar_smul_right, QuadraticMap.polar_smul_right, hbb]
        simpa using mul_ne_zero hd hbz
      have hawDiff : Q (a.1 - w) ≠ 0 := by
        rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg,
          QuadraticMap.polar_neg_right, hwq]
        intro hzero
        apply haw
        linear_combination Q a.1 * htwo - hzero
      have hwbDiff : Q (w - b') ≠ 0 := by
        rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg,
          QuadraticMap.polar_neg_right, hwq, ← heq]
        intro hzero
        apply hbw
        rw [QuadraticMap.polar_comm]
        linear_combination Q a.1 * htwo - hzero
      let aw : AnisotropicVector Q := ⟨a.1 - w, hawDiff⟩
      let wb : AnisotropicVector Q := ⟨w - b', hwbDiff⟩
      refine ⟨symmetryPoint wb * symmetryPoint aw, c, hc0, ?_⟩
      change (symmetryPoint wb).1 ((symmetryPoint aw).1 a.1) = c • b.1
      rw [symmetryPoint_apply, symmetryPoint_apply]
      change conjugationSymmetry Q (w - b') hwbDiff
        (conjugationSymmetry Q (a.1 - w) hawDiff a.1) = _
      rw [conjugationSymmetry_maps_eq_neg a.1 w hwq.symm hawDiff,
        map_neg, conjugationSymmetry_maps_eq_neg w b'
          (hwq.trans heq) hwbDiff]
      have hnegOne : (-1 : k) = 1 := by
        apply neg_eq_iff_add_eq_zero.mpr
        norm_num at htwo ⊢
        exact htwo
      have hneg (v : V) : -v = v := by
        calc
          -v = (-1 : k) • v := by simp
          _ = (1 : k) • v := by rw [hnegOne]
          _ = v := one_smul k v
      simp only [hneg, b']

omit [IsAlgClosed k] [FiniteDimensional k V] in
private lemma conjugationSymmetry_equivariant
    (g : quadraticIsometrySubgroup Q) (a : V) (ha : Q a ≠ 0) (v : V) :
    g.1 (conjugationSymmetry Q a ha v) =
      conjugationSymmetry Q (g.1 a)
        (by
          rw [(mem_quadraticIsometrySubgroup Q g.1).1 g.2 a]
          exact ha) (g.1 v) := by
  have hQ (x : V) : Q (g.1 x) = Q x :=
    (mem_quadraticIsometrySubgroup Q g.1).1 g.2 x
  have hpolar : QuadraticMap.polar Q (g.1 a) (g.1 v) =
      QuadraticMap.polar Q a v := by
    simp only [QuadraticMap.polar, ← map_add]
    rw [hQ, hQ, hQ]
  rw [conjugationSymmetry_apply, conjugationSymmetry_apply]
  change g.1 (((Q a)⁻¹ * QuadraticMap.polar Q a v) • a - v) = _
  rw [map_sub, map_smul, hQ, hpolar]

private lemma symmetryPoint_conjugate
    (s : SplitQuadraticForm Q) (a b : AnisotropicVector Q) :
    ∃ g : quadraticIsometrySubgroup Q,
      symmetryPoint b = g * symmetryPoint a * g⁻¹ := by
  obtain ⟨g, c, hc, hga⟩ := exists_isometry_maps_anisotropic_line s a b
  refine ⟨g, ?_⟩
  apply Subtype.ext
  ext v
  change conjugationSymmetry Q b.1 b.2 v =
    g.1 (conjugationSymmetry Q a.1 a.2 ((g⁻¹).1 v))
  rw [conjugationSymmetry_equivariant]
  have hcancel : g.1 ((g⁻¹).1 v) = v := by
    exact LinearEquiv.apply_symm_apply g.1 v
  rw [hcancel]
  rw [conjugationSymmetry_apply, conjugationSymmetry_apply, hga]
  simp only [QuadraticMap.map_smul, QuadraticMap.polar_smul_left, smul_smul]
  apply congrArg (fun z : k => z • b.1 - v)
  field_simp [hc, b.2]
  ring

/-- A product of two conjugation symmetries belongs to the derived subgroup of
the split quadratic-isometry group. -/
public lemma symmetryPair_mem_commutator
    (s : SplitQuadraticForm Q) (a b : AnisotropicVector Q) :
    symmetryPoint a * symmetryPoint b ∈
      commutator (quadraticIsometrySubgroup Q) := by
  obtain ⟨g, hconj⟩ := symmetryPoint_conjugate s b a
  have hmem : ⁅g, symmetryPoint b⁆ ∈
      commutator (quadraticIsometrySubgroup Q) :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top g)
      (Subgroup.mem_top (symmetryPoint b))
  have heq : ⁅g, symmetryPoint b⁆ = symmetryPoint a * symmetryPoint b := by
    rw [commutatorElement_def, symmetryPoint_inv, ← hconj]
  rwa [heq] at hmem

omit [IsAlgClosed k] [FiniteDimensional k V] in
private lemma symmetryProductPoint_append
    (as bs : List (AnisotropicVector Q)) :
    symmetryProductPoint (as ++ bs) =
      symmetryProductPoint as * symmetryProductPoint bs := by
  simp [symmetryProductPoint, List.map_append, List.prod_append]

omit [IsAlgClosed k] [FiniteDimensional k V] in
private lemma symmetryProductPoint_reverse
    (as : List (AnisotropicVector Q)) :
    symmetryProductPoint as.reverse = (symmetryProductPoint as)⁻¹ := by
  induction as with
  | nil => simp [symmetryProductPoint]
  | cons a as ih =>
      rw [List.reverse_cons, symmetryProductPoint_append, ih]
      simp [symmetryProductPoint, symmetryPoint_inv]

private lemma even_symmetryProductPoint_mem_commutator
    (s : SplitQuadraticForm Q) (as : List (AnisotropicVector Q))
    (has : Even as.length) :
    symmetryProductPoint as ∈ commutator (quadraticIsometrySubgroup Q) := by
  induction as using List.twoStepInduction with
  | nil => simp [symmetryProductPoint]
  | singleton a => simp at has
  | cons_cons a b as ih =>
      have has' : Even as.length := by
        obtain ⟨n, hn⟩ := has
        refine ⟨n - 1, ?_⟩
        simp only [List.length_cons] at hn
        omega
      change symmetryPoint a * symmetryPoint b * symmetryProductPoint as ∈ _
      exact mul_mem (symmetryPair_mem_commutator s a b) (ih has')

omit [IsAlgClosed k] [FiniteDimensional k V] in
@[simp] public lemma symmetryProductPoint_nil :
    symmetryProductPoint ([] : List (AnisotropicVector Q)) = 1 := by
  simp [symmetryProductPoint]

omit [IsAlgClosed k] [FiniteDimensional k V] in
public lemma symmetryProductPoint_cons (a : AnisotropicVector Q)
    (as : List (AnisotropicVector Q)) :
    symmetryProductPoint (a :: as) = symmetryPoint a * symmetryProductPoint as := by
  simp [symmetryProductPoint]

/-- The image of the split even Clifford Spin action is exactly the abstract
commutator subgroup of the full quadratic isometry group. -/
public theorem cliffordSpinActionOfSplit_range_eq_commutator
    (s : SplitQuadraticForm Q) (hrank : 4 ≤ s.rank) :
    (cliffordSpinActionOfSplit Q s).range =
      commutator (quadraticIsometrySubgroup Q) := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    obtain ⟨as, has⟩ := exists_symmetryFactorization s
      (cliffordSpinActionOfSplit Q s x)
    have hrank0 : 0 < s.rank := lt_of_lt_of_le (by omega) hrank
    have hasEven := symmetryFactorization_even_of_spinAction
      s hrank0 x as has
    rw [← has]
    exact even_symmetryProductPoint_mem_commutator s as hasEven
  · rw [commutator_eq_closure]
    refine (Subgroup.closure_le _).2 ?_
    intro y hy
    rw [mem_commutatorSet_iff] at hy
    obtain ⟨g, h, rfl⟩ := hy
    obtain ⟨as, has⟩ := exists_symmetryFactorization s g
    obtain ⟨bs, hbs⟩ := exists_symmetryFactorization s h
    let cs := as ++ bs ++ as.reverse ++ bs.reverse
    have hcsEven : Even cs.length := by
      refine ⟨as.length + bs.length, ?_⟩
      simp [cs]
      omega
    refine ⟨evenSymmetrySpinLift cs hcsEven, ?_⟩
    rw [evenSymmetrySpinLift_action]
    simp only [cs, symmetryProductPoint_append, symmetryProductPoint_reverse,
      has, hbs, commutatorElement_def]

/-- Every element of the split quadratic-isometry derived subgroup admits an
even conjugation-symmetry factorization. -/
public theorem exists_even_symmetryFactorization_of_mem_commutator
    (s : SplitQuadraticForm Q) (hrank : 4 ≤ s.rank)
    {g : quadraticIsometrySubgroup Q}
    (hg : g ∈ commutator (quadraticIsometrySubgroup Q)) :
    ∃ as : List (AnisotropicVector Q),
      Even as.length ∧ symmetryProductPoint as = g := by
  rw [← cliffordSpinActionOfSplit_range_eq_commutator s hrank] at hg
  obtain ⟨x, rfl⟩ := hg
  obtain ⟨as, has⟩ := exists_symmetryFactorization s
    (cliffordSpinActionOfSplit Q s x)
  refine ⟨as, ?_, has⟩
  exact symmetryFactorization_even_of_spinAction s (by omega) x as has

end Theory.AlgebraicGroup
