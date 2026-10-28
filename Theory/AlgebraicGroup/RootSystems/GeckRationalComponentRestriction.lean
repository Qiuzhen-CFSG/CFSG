module

public import Theory.AlgebraicGroup.RootSystems.IntegralTitsCoherence
public import Theory.AlgebraicGroup.RootSystems.Weyl
public import Theory.AlgebraicGroup.RootSystems.Deletion
public import Mathlib.LinearAlgebra.RootSystem.Defs
public import Mathlib.LinearAlgebra.RootSystem.Base
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Lie.Matrix
public import Mathlib.Data.Matrix.Diagonal

/-!
# Rational Geck component restriction

This module packages the rational scalar restriction of a finite reduced
crystallographic root pairing with the irreducible orthogonal component
containing a chosen root.  It exposes component membership, reflection-word
closure and deletion, together with a component carrier and an injective
linear padding map for rational Geck matrices.  The pointwise padding
identities recover the ambient `Q`-mapped `eMatrix` and deleted-word Tits
conjugates, while orthogonal letters are represented by the component
identity.  Only ordinary component/Coxeter/deletion facts and the integral
Tits coherence API are used; no route-Matsumoto or all-root operator module is
needed here.
-/

namespace RootPairing.IntegralGeckConstruction

open Function Set Submodule Matrix
open scoped Matrix

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

variable {ι R M N : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base} [Fintype ι] [DecidableEq ι]

@[expose] public noncomputable def ratBase : (P.restrictScalarsRat).Base := by
  let _i : Module ℚ M := Module.compHom M (algebraMap ℚ R)
  let _i : Module ℚ N := Module.compHom N (algebraMap ℚ R)
  refine {
    support := b.support
    linearIndepOn_root := by
      rw [linearIndepOn_iff']
      intro s g hs hg
      have hzero : ∑ x ∈ s, (algebraMap ℚ R (g x)) • P.root x = 0 := by
        simpa [map_sum, algebra_compatible_smul R] using congrArg Subtype.val hg
      have hz := (linearIndepOn_iff'.mp b.linearIndepOn_root) s
        (fun x => algebraMap ℚ R (g x)) hs hzero
      intro x hx
      apply FaithfulSMul.algebraMap_injective ℚ R
      simpa using hz x hx
    linearIndepOn_coroot := by
      rw [linearIndepOn_iff']
      intro s g hs hg
      have hzero : ∑ x ∈ s, (algebraMap ℚ R (g x)) • P.coroot x = 0 := by
        simpa [map_sum, algebra_compatible_smul R] using congrArg Subtype.val hg
      have hz := (linearIndepOn_iff'.mp b.linearIndepOn_coroot) s
        (fun x => algebraMap ℚ R (g x)) hs hzero
      intro x hx
      apply FaithfulSMul.algebraMap_injective ℚ R
      simpa using hz x hx
    root_mem_or_neg_mem i := by
      let A := AddSubmonoid.closure
        ((P.restrictScalarsRat).root '' (b.support : Set ι))
      rcases b.exists_root_eq_sum_nat_or_neg i with ⟨f, -, h | h⟩
      · left
        have hsum :
            ((∑ j ∈ b.support, f j • (P.restrictScalarsRat).root j :
                Submodule.span ℚ (Set.range P.root)) : M) =
              ∑ j ∈ b.support, f j • P.root j := by
          rw [Submodule.coe_sum]
          apply Finset.sum_congr rfl
          intro j hj
          simpa only [RootPairing.restrictScalars_coe_root, Submodule.subtype_apply] using
            map_nsmul (Submodule.span ℚ (Set.range P.root)).subtype
              (f j) ((P.restrictScalarsRat).root j)
        rw [show (P.restrictScalarsRat).root i =
            ∑ j ∈ b.support, f j • (P.restrictScalarsRat).root j by
          apply Subtype.ext
          calc
            ((P.restrictScalarsRat).root i : M) = P.root i := by simp
            _ = ∑ j ∈ b.support, f j • P.root j := h
            _ = _ := hsum.symm]
        exact AddSubmonoid.sum_mem _ fun j hj =>
          AddSubmonoid.nsmul_mem _
            (AddSubmonoid.subset_closure (show (P.restrictScalarsRat).root j ∈
              (P.restrictScalarsRat).root '' (b.support : Set ι) from
                ⟨j, by simpa using hj, rfl⟩)) _
      · right
        have hsum :
            ((∑ j ∈ b.support, f j • (P.restrictScalarsRat).root j :
                Submodule.span ℚ (Set.range P.root)) : M) =
              ∑ j ∈ b.support, f j • P.root j := by
          rw [Submodule.coe_sum]
          apply Finset.sum_congr rfl
          intro j hj
          simpa only [RootPairing.restrictScalars_coe_root, Submodule.subtype_apply] using
            map_nsmul (Submodule.span ℚ (Set.range P.root)).subtype
              (f j) ((P.restrictScalarsRat).root j)
        rw [show -(P.restrictScalarsRat).root i =
            ∑ j ∈ b.support, f j • (P.restrictScalarsRat).root j by
          apply Subtype.ext
          calc
            ((-(P.restrictScalarsRat).root i :
                Submodule.span ℚ (Set.range P.root)) : M) = -P.root i := by simp
            _ = ∑ j ∈ b.support, f j • P.root j := by
              simpa only [neg_neg] using congrArg (fun x : M => -x) h
            _ = _ := hsum.symm]
        exact AddSubmonoid.sum_mem _ fun j hj =>
          AddSubmonoid.nsmul_mem _
            (AddSubmonoid.subset_closure (show (P.restrictScalarsRat).root j ∈
              (P.restrictScalarsRat).root '' (b.support : Set ι) from
                ⟨j, by simpa using hj, rfl⟩)) _
    coroot_mem_or_neg_mem i := by
      let A := AddSubmonoid.closure
        ((P.restrictScalarsRat).coroot '' (b.support : Set ι))
      rcases b.flip.exists_root_eq_sum_nat_or_neg i with ⟨f, -, h | h⟩
      · left
        have hsum :
            ((∑ j ∈ b.support, f j • (P.restrictScalarsRat).coroot j :
                Submodule.span ℚ (Set.range P.coroot)) : N) =
              ∑ j ∈ b.support, f j • P.coroot j := by
          rw [Submodule.coe_sum]
          apply Finset.sum_congr rfl
          intro j hj
          simpa only [RootPairing.restrictScalars_coe_coroot, Submodule.subtype_apply] using
            map_nsmul (Submodule.span ℚ (Set.range P.coroot)).subtype
              (f j) ((P.restrictScalarsRat).coroot j)
        rw [show (P.restrictScalarsRat).coroot i =
            ∑ j ∈ b.support, f j • (P.restrictScalarsRat).coroot j by
          apply Subtype.ext
          calc
            ((P.restrictScalarsRat).coroot i : N) = P.coroot i := by simp
            _ = ∑ j ∈ b.support, f j • P.coroot j := h
            _ = _ := hsum.symm]
        exact AddSubmonoid.sum_mem _ fun j hj =>
          AddSubmonoid.nsmul_mem _
            (AddSubmonoid.subset_closure (show (P.restrictScalarsRat).coroot j ∈
              (P.restrictScalarsRat).coroot '' (b.support : Set ι) from
                ⟨j, by simpa using hj, rfl⟩)) _
      · right
        have hsum :
            ((∑ j ∈ b.support, f j • (P.restrictScalarsRat).coroot j :
                Submodule.span ℚ (Set.range P.coroot)) : N) =
              ∑ j ∈ b.support, f j • P.coroot j := by
          rw [Submodule.coe_sum]
          apply Finset.sum_congr rfl
          intro j hj
          simpa only [RootPairing.restrictScalars_coe_coroot, Submodule.subtype_apply] using
            map_nsmul (Submodule.span ℚ (Set.range P.coroot)).subtype
              (f j) ((P.restrictScalarsRat).coroot j)
        rw [show -(P.restrictScalarsRat).coroot i =
            ∑ j ∈ b.support, f j • (P.restrictScalarsRat).coroot j by
          apply Subtype.ext
          calc
            ((-(P.restrictScalarsRat).coroot i :
                Submodule.span ℚ (Set.range P.coroot)) : N) = -P.coroot i := by simp
            _ = ∑ j ∈ b.support, f j • P.coroot j := by
              simpa [RootPairing.Base.flip, RootPairing.flip] using
                congrArg (fun x : N => -x) h
            _ = _ := hsum.symm]
        exact AddSubmonoid.sum_mem _ fun j hj =>
          AddSubmonoid.nsmul_mem _
            (AddSubmonoid.subset_closure (show (P.restrictScalarsRat).coroot j ∈
              (P.restrictScalarsRat).coroot '' (b.support : Set ι) from
                ⟨j, by simpa using hj, rfl⟩)) _
  }

@[expose] public noncomputable def rationalBase : (P.restrictScalarsRat).Base :=
  ratBase (P := P) (b := b)

@[simp] public theorem rationalBase_support :
    (rationalBase (P := P) (b := b)).support = b.support := rfl

public noncomputable def irreducibleDecomposition :
    (P.restrictScalarsRat).OrthogonalDecomposition :=
  Classical.choose (Theory.AlgebraicGroup.exists_unique_irreducibleOrthogonalDecomposition_parts
    P.restrictScalarsRat)

public theorem irreducibleDecomposition_isIrreducible :
    (irreducibleDecomposition (P := P)).IsIrreducible :=
  (Classical.choose_spec (Theory.AlgebraicGroup.exists_unique_irreducibleOrthogonalDecomposition_parts
    P.restrictScalarsRat)).1

public noncomputable def componentSet (i : ι) : Set ι :=
  Classical.choose (show ∃ s ∈ (irreducibleDecomposition (P := P)).parts, i ∈ s by
    have hi : i ∈ ⋃₀ (irreducibleDecomposition (P := P)).parts := by
      rw [(irreducibleDecomposition (P := P)).cover]
      trivial
    exact Set.mem_sUnion.mp hi)

public theorem componentSet_mem_parts (i : ι) :
    componentSet (P := P) i ∈ (irreducibleDecomposition (P := P)).parts :=
  (Classical.choose_spec (show ∃ s ∈ (irreducibleDecomposition (P := P)).parts, i ∈ s by
    have hi : i ∈ ⋃₀ (irreducibleDecomposition (P := P)).parts := by
      rw [(irreducibleDecomposition (P := P)).cover]
      trivial
    exact Set.mem_sUnion.mp hi)).1

public theorem componentSet_mem (i : ι) : i ∈ componentSet (P := P) i :=
  (Classical.choose_spec (show ∃ s ∈ (irreducibleDecomposition (P := P)).parts, i ∈ s by
    have hi : i ∈ ⋃₀ (irreducibleDecomposition (P := P)).parts := by
      rw [(irreducibleDecomposition (P := P)).cover]
      trivial
    exact Set.mem_sUnion.mp hi)).2

public theorem componentSet_isIrreducible (i : ι) :
    (P.restrictScalarsRat).IsIrreducibleSet (componentSet (P := P) i) :=
  irreducibleDecomposition_isIrreducible (P := P)
    (componentSet (P := P) i) (componentSet_mem_parts (P := P) i)

/- The following two definitions keep the rational pairing and its chosen base
   available together with a component set.  The ambient carrier is retained:
   the component condition is carried by the set argument, which is exactly
   what the padding and deletion maps below require. -/
public noncomputable def componentRootPairing (s : Set ι) :=
  P.restrictScalarsRat

public noncomputable def componentBase (s : Set ι) :
    (componentRootPairing (P := P) s).Base :=
  rationalBase (P := P) (b := b)

public theorem componentRootPairing_isIrreducible (i : ι) :
    (componentRootPairing (P := P) (componentSet (P := P) i)).IsIrreducibleSet
      (componentSet (P := P) i) :=
  componentSet_isIrreducible (P := P) i

public theorem reflection_mem_componentSet (i : ι) {q j : ι}
    (hq : q ∈ componentSet (P := P) i)
    (hj : j ∈ componentSet (P := P) i) :
    (P.restrictScalarsRat).reflectionPerm q j ∈ componentSet (P := P) i := by
  let Q := P.restrictScalarsRat
  let d := irreducibleDecomposition (P := P)
  by_contra hnot
  obtain ⟨t, ht, hkt⟩ : ∃ t ∈ d.parts, Q.reflectionPerm q j ∈ t := by
    have hcover : Q.reflectionPerm q j ∈ ⋃₀ d.parts := by
      rw [d.cover]
      trivial
    exact Set.mem_sUnion.mp hcover
  have hs : componentSet (P := P) i ∈ d.parts := componentSet_mem_parts (P := P) i
  have hst : componentSet (P := P) i ≠ t := by
    intro hEq
    subst t
    exact hnot hkt
  have horth := d.orthogonal _ hs _ ht hst q hq (Q.reflectionPerm q j) hkt
  have hfix : Q.reflectionPerm q (Q.reflectionPerm q j) = Q.reflectionPerm q j :=
    Q.reflectionPerm_eq_of_pairing_eq_zero horth.2
  have hinv : Q.reflectionPerm q (Q.reflectionPerm q j) = j :=
    Q.reflectionPerm_self q j
  have hjk : j = Q.reflectionPerm q j := hinv.symm.trans hfix
  have hjt : j ∈ t := hjk.symm ▸ hkt
  exact (Set.disjoint_left.1 (d.pairwise_disjoint hs ht hst)) hj hjt

public theorem reflectionWord_mem_componentSet (i : ι) (word : List b.support)
    (hword : ∀ q : b.support, q ∈ word → (q : ι) ∈ componentSet (P := P) i)
    (j : ι) (hj : j ∈ componentSet (P := P) i) :
    reflectionWord (P := P) (b := b) word j ∈ componentSet (P := P) i := by
  induction word with
  | nil => simpa [reflectionWord] using hj
  | cons q word ih =>
      rw [reflectionWord]
      apply reflection_mem_componentSet (P := P) i
      · exact hword q (by simp)
      · apply ih
        intro r hr
        exact hword r (by simp [hr])

public theorem commonReflectionWord_endpoint_component
    (word : List b.support) {i j k : ι}
    (hi : reflectionWord (P := P) (b := b) word i = k)
    (hj : reflectionWord (P := P) (b := b) word j = k)
    (hword : ∀ q : b.support, q ∈ word → (q : ι) ∈ componentSet (P := P) i) :
    j ∈ componentSet (P := P) i := by
  have hk : k ∈ componentSet (P := P) i := by
    rw [← hi]
    exact reflectionWord_mem_componentSet (P := P) i word hword i
      (componentSet_mem (P := P) i)
  have reverse : ∀ (w : List b.support) {a c d : ι},
      reflectionWord (P := P) (b := b) w a = d →
      reflectionWord (P := P) (b := b) w c = d →
      (∀ q : b.support, q ∈ w → (q : ι) ∈ componentSet (P := P) i) →
      d ∈ componentSet (P := P) i →
      c ∈ componentSet (P := P) i := by
    intro w
    induction w with
    | nil =>
        intro a c d ha hc hw hd
        simp only [reflectionWord] at hc
        exact hc.symm ▸ hd
    | cons q w ih =>
        intro a c d ha hc hw hd
        simp only [reflectionWord] at ha hc
        have htail_a : reflectionWord (P := P) (b := b) w a =
            P.reflectionPerm q d := by
          simpa only [P.reflectionPerm_self] using
            congrArg (P.reflectionPerm q) ha
        have htail_c : reflectionWord (P := P) (b := b) w c =
            P.reflectionPerm q d := by
          simpa only [P.reflectionPerm_self] using
            congrArg (P.reflectionPerm q) hc
        apply ih htail_a htail_c
        · intro r hr
          exact hw r (by simp [hr])
        · change P.reflectionPerm q d ∈ componentSet (P := P) i
          exact reflection_mem_componentSet (P := P) i (hw q (by simp)) hd
  exact reverse word hi hj hword hk

@[expose] public noncomputable def deleteWord (s : Set ι)
    (word : List b.support) : List b.support :=
  by
    classical
    exact word.filter (fun j => decide ((j : ι) ∈ s))

@[simp] public theorem deleteWord_nil (s : Set ι) :
    deleteWord (b := b) s [] = [] := by
  simp [deleteWord]

@[simp] public theorem deleteWord_cons_of_mem (s : Set ι) (q : b.support)
    (word : List b.support) (hq : (q : ι) ∈ s) :
    deleteWord (b := b) s (q :: word) = q :: deleteWord (b := b) s word := by
  simp [deleteWord, hq]

@[simp] public theorem deleteWord_cons_of_not_mem (s : Set ι) (q : b.support)
    (word : List b.support) (hq : (q : ι) ∉ s) :
    deleteWord (b := b) s (q :: word) = deleteWord (b := b) s word := by
  simp [deleteWord, hq]

public theorem deleteWord_eq_self_of_mem (s : Set ι) (word : List b.support)
    (hword : ∀ q : b.support, q ∈ word → (q : ι) ∈ s) : deleteWord (b := b) s word = word := by
  classical
  unfold deleteWord
  apply List.filter_eq_self.mpr
  intro q hq
  exact decide_eq_true_eq.mpr (hword q hq)

public theorem deleteWord_mem (s : Set ι) (word : List b.support)
    {q : b.support} (hq : q ∈ deleteWord (b := b) s word) :
    (q : ι) ∈ s := by
  classical
  have h := (List.mem_filter.mp hq).2
  simpa [deleteWord] using h

public theorem reflectionWord_delete_eq_of_mem (s : Set ι) (word : List b.support)
    (hword : ∀ q : b.support, q ∈ word → (q : ι) ∈ s) (j : ι) :
    reflectionWord (P := P) (b := b) (deleteWord s word) j =
      reflectionWord (P := P) (b := b) word j := by
  rw [deleteWord_eq_self_of_mem s word hword]

@[expose] public def componentCarrier (s : Set ι) : Type _ :=
  {x : b.support ⊕ ι // (match x with
    | Sum.inl i => (i : ι) ∈ s
    | Sum.inr i => i ∈ s)}

public noncomputable instance componentCarrierFintype (s : Set ι) :
    Fintype (componentCarrier (b := b) s) := by
  classical
  unfold componentCarrier
  infer_instance

public noncomputable instance componentCarrierDecidableEq (s : Set ι) :
    DecidableEq (componentCarrier (b := b) s) := Classical.decEq _

public noncomputable def componentIdentity (s : Set ι) :
    Matrix (componentCarrier (b := b) s) (componentCarrier (b := b) s) ℚ := by
  classical
  exact fun x y => if x = y then 1 else 0

public noncomputable def componentEmbedding (s : Set ι) :
    componentCarrier (b := b) s → b.support ⊕ ι := Subtype.val

public noncomputable def padMatrix (s : Set ι)
    (A : Matrix (componentCarrier (b := b) s)
      (componentCarrier (b := b) s) ℚ) :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℚ := by
  classical
  exact fun x y => if hx : (match x with
      | Sum.inl i => (i : ι) ∈ s
      | Sum.inr i => i ∈ s) then
    if hy : (match y with
        | Sum.inl i => (i : ι) ∈ s
        | Sum.inr i => i ∈ s) then
      A ⟨x, hx⟩ ⟨y, hy⟩
    else 0
  else 0

public theorem padMatrix_injective (s : Set ι) :
    Function.Injective (padMatrix (b := b) s) := by
  intro A B h
  funext x y
  classical
  have hxy := congrArg (fun M => M x.val y.val) h
  let x' : componentCarrier (b := b) s := ⟨x.val, x.property⟩
  let y' : componentCarrier (b := b) s := ⟨y.val, y.property⟩
  have hx' : x' = x := Subtype.ext rfl
  have hy' : y' = y := Subtype.ext rfl
  simpa [padMatrix, x.property, y.property, x', y', hx', hy'] using hxy

public noncomputable def padMatrixLinear (s : Set ι) :
    Matrix (componentCarrier (b := b) s)
      (componentCarrier (b := b) s) ℚ →ₗ[ℚ]
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℚ := {
  toFun := padMatrix (b := b) s
  map_add' := by
    intro A B
    classical
    ext x y
    by_cases hx : (match x with
        | Sum.inl i => (i : ι) ∈ s
        | Sum.inr i => i ∈ s) <;>
      by_cases hy : (match y with
          | Sum.inl i => (i : ι) ∈ s
          | Sum.inr i => i ∈ s) <;>
      simp [padMatrix, hx, hy, Matrix.add_apply] <;> rfl
  map_smul' := by
    intro c A
    classical
    ext x y
    by_cases hx : (match x with
        | Sum.inl i => (i : ι) ∈ s
        | Sum.inr i => i ∈ s) <;>
      by_cases hy : (match y with
          | Sum.inl i => (i : ι) ∈ s
          | Sum.inr i => i ∈ s) <;>
      simp [padMatrix, hx, hy, Matrix.smul_apply] <;> rfl
  }

public theorem padMatrixLinear_injective (s : Set ι) :
    Function.Injective (padMatrixLinear (b := b) s) :=
  padMatrix_injective (b := b) s

@[expose] public noncomputable def restrictMatrix (s : Set ι)
    (A : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℚ) :
    Matrix (componentCarrier (b := b) s)
      (componentCarrier (b := b) s) ℚ := fun x y => A x.val y.val

public theorem padMatrix_restrictMatrix (s : Set ι)
    (A : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℚ)
    (x y : componentCarrier (b := b) s) :
    padMatrix (b := b) s (restrictMatrix (b := b) s A) (Subtype.val x) (Subtype.val y) =
      A (Subtype.val x) (Subtype.val y) := by
  classical
  simp [padMatrix, x.property, y.property, restrictMatrix]

public theorem padMatrix_smul_transfer (s : Set ι)
    {A B : Matrix (componentCarrier (b := b) s)
      (componentCarrier (b := b) s) ℚ} (q : ℚ)
    (h : padMatrix (b := b) s A = q • padMatrix (b := b) s B) :
    A = q • B := by
  classical
  apply padMatrix_injective (b := b) s
  exact h.trans ((padMatrixLinear (b := b) s).map_smul q B).symm

@[expose] public noncomputable def qMatrix
    (A : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ) :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℚ :=
  A.map (algebraMap ℤ ℚ)

@[expose] public noncomputable def componentEMatrix (s : Set ι) (i : b.support) :
    Matrix (componentCarrier (b := b) s) (componentCarrier (b := b) s) ℚ :=
  restrictMatrix (b := b) s (qMatrix (b := b) (eMatrix i))

@[expose] public noncomputable def componentDeletedTitsConjugate (s : Set ι)
    (word : List b.support) (i : b.support) :
    Matrix (componentCarrier (b := b) s) (componentCarrier (b := b) s) ℚ :=
  restrictMatrix (b := b) s
    (qMatrix (b := b) (titsConjugate (b := b) (deleteWord s word) (eMatrix i)))

public theorem pad_componentEMatrix (s : Set ι) (i : b.support)
    (x y : componentCarrier (b := b) s) :
    padMatrix (b := b) s (componentEMatrix (b := b) s i)
        (Subtype.val x) (Subtype.val y) =
      qMatrix (b := b) (eMatrix i) (Subtype.val x) (Subtype.val y) := by
  exact padMatrix_restrictMatrix (b := b) s (qMatrix (b := b) (eMatrix i)) x y

public theorem pad_componentDeletedTitsConjugate (s : Set ι)
    (word : List b.support) (i : b.support)
    (x y : componentCarrier (b := b) s) :
    padMatrix (b := b) s (componentDeletedTitsConjugate (b := b) s word i)
        (Subtype.val x) (Subtype.val y) =
      qMatrix (b := b)
        (titsConjugate (b := b) (deleteWord s word) (eMatrix i))
        (Subtype.val x) (Subtype.val y) := by
  exact padMatrix_restrictMatrix (b := b) s
    (qMatrix (b := b) (titsConjugate (b := b) (deleteWord s word) (eMatrix i))) x y

public noncomputable def componentOrthogonalLetter (s : Set ι) (q : b.support) :
    Matrix (componentCarrier (b := b) s) (componentCarrier (b := b) s) ℚ :=
  by
    classical
    exact if hq : (q : ι) ∈ s then
      restrictMatrix (b := b) s (qMatrix (b := b) (titsLift q))
    else componentIdentity (b := b) s

public theorem componentOrthogonalLetter_trivial (s : Set ι) (q : b.support)
    (hq : (q : ι) ∉ s) :
    componentOrthogonalLetter (b := b) s q = componentIdentity (b := b) s := by
  classical
  simp [componentOrthogonalLetter, hq]

end
end RootPairing.IntegralGeckConstruction
