module

public import Theory.AlgebraicGroup.RootSystems.GeckScalarExtension

/-!
# Compatibility of scalar extension with integral Tits matrices

The coordinate scalar extension from `GeckScalarExtension` preserves root strings, the integral
Geck matrices, and the Tits words built from them.  In particular, `eMatrix`,
`titsConjugate`, and `reflectionWord` compute identically before and after extension to an
algebraic closure of `ℚ`.  These identities are the descent interface used by rational
root-space multiplicity one.
-/

namespace RootPairing.IntegralGeckConstruction

open Function Matrix Set Submodule

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

local instance : Algebra ℤ RatAlgClosure := Ring.toIntAlgebra RatAlgClosure

variable {ι R M N : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsCrystallographic]
  [P.IsReduced] [P.IsIrreducible]
  {b : P.Base} [Fintype ι] [DecidableEq ι]

@[simp] private lemma scalarExtension_pairingIn (i j : ι) :
    (scalarExtension (P := P) (b := b)).pairingIn ℤ i j = P.pairingIn ℤ i j := by
  apply FaithfulSMul.algebraMap_injective ℤ RatAlgClosure
  rw [(scalarExtension (P := P) (b := b)).algebraMap_pairingIn ℤ]
  change dotProduct (scalarExtensionRoot (P := P) (b := b) i)
      (scalarExtensionCoroot (P := P) (b := b) j) =
    algebraMap ℤ RatAlgClosure (P.pairingIn ℤ i j)
  exact scalarExtension_pairing (P := P) (b := b) i j

/-- The additive embedding of the integral root lattice into scalar-extension coordinates. -/
private def scalarExtensionRootSpan :
    P.rootSpan ℤ →+ (b.support → RatAlgClosure) where
  toFun x k := algebraMap ℤ RatAlgClosure (b.toWeightBasisInt.repr x k)
  map_zero' := by
    ext k
    simp
  map_add' x y := by
    ext k
    simp

@[simp] private lemma scalarExtensionRootSpan_root (i : ι) :
    scalarExtensionRootSpan (P := P) (b := b) (P.rootSpanMem ℤ i) =
      scalarExtensionRoot (P := P) (b := b) i := rfl

private lemma scalarExtensionRootSpan_injective :
    Injective (scalarExtensionRootSpan (P := P) (b := b)) := by
  intro x y hxy
  apply b.toWeightBasisInt.repr.injective
  ext k
  apply FaithfulSMul.algebraMap_injective ℤ RatAlgClosure
  exact congrFun hxy k

private lemma scalarExtension_root_eq_add_nsmul_iff
    {i j k : ι} {n : ℕ} :
    (scalarExtension (P := P) (b := b)).root k =
        (scalarExtension (P := P) (b := b)).root j +
          n • (scalarExtension (P := P) (b := b)).root i ↔
      P.root k = P.root j + n • P.root i := by
  change scalarExtensionRoot (P := P) (b := b) k =
      scalarExtensionRoot (P := P) (b := b) j +
        n • scalarExtensionRoot (P := P) (b := b) i ↔ _
  constructor
  · intro h
    have hspan : P.rootSpanMem ℤ k =
        P.rootSpanMem ℤ j + n • P.rootSpanMem ℤ i := by
      apply scalarExtensionRootSpan_injective (P := P) (b := b)
      simpa only [map_add, map_nsmul, scalarExtensionRootSpan_root] using h
    exact congrArg Subtype.val hspan
  · intro h
    have hspan : P.rootSpanMem ℤ k =
        P.rootSpanMem ℤ j + n • P.rootSpanMem ℤ i := by
      apply Subtype.ext
      simpa using h
    simpa only [map_add, map_nsmul, scalarExtensionRootSpan_root] using
      congrArg (scalarExtensionRootSpan (P := P) (b := b)) hspan

private lemma scalarExtension_root_eq_sub_nsmul_iff
    {i j k : ι} {n : ℕ} :
    (scalarExtension (P := P) (b := b)).root k =
        (scalarExtension (P := P) (b := b)).root j -
          n • (scalarExtension (P := P) (b := b)).root i ↔
      P.root k = P.root j - n • P.root i := by
  change scalarExtensionRoot (P := P) (b := b) k =
      scalarExtensionRoot (P := P) (b := b) j -
        n • scalarExtensionRoot (P := P) (b := b) i ↔ _
  constructor
  · intro h
    have hspan : P.rootSpanMem ℤ k =
        P.rootSpanMem ℤ j - n • P.rootSpanMem ℤ i := by
      apply scalarExtensionRootSpan_injective (P := P) (b := b)
      simpa only [map_sub, map_nsmul, scalarExtensionRootSpan_root] using h
    exact congrArg Subtype.val hspan
  · intro h
    have hspan : P.rootSpanMem ℤ k =
        P.rootSpanMem ℤ j - n • P.rootSpanMem ℤ i := by
      apply Subtype.ext
      simpa using h
    simpa only [map_sub, map_nsmul, scalarExtensionRootSpan_root] using
      congrArg (scalarExtensionRootSpan (P := P) (b := b)) hspan

@[simp] private lemma scalarExtension_root_eq_add_iff {i j k : ι} :
    (scalarExtension (P := P) (b := b)).root k =
        (scalarExtension (P := P) (b := b)).root i +
          (scalarExtension (P := P) (b := b)).root j ↔
      P.root k = P.root i + P.root j := by
  simpa only [one_nsmul] using
    (scalarExtension_root_eq_add_nsmul_iff (P := P) (b := b)
      (i := j) (j := i) (k := k) (n := 1))

@[simp] private lemma scalarExtension_reflectionPerm (i j : ι) :
    (scalarExtension (P := P) (b := b)).reflectionPerm i j =
      P.reflectionPerm i j := rfl

private lemma scalarExtension_root_eq_neg_iff {i j : ι} :
    (scalarExtension (P := P) (b := b)).root i =
        -(scalarExtension (P := P) (b := b)).root j ↔
      P.root i = -P.root j := by
  change scalarExtensionRoot (P := P) (b := b) i =
      -scalarExtensionRoot (P := P) (b := b) j ↔ _
  constructor
  · intro h
    have hspan : P.rootSpanMem ℤ i = -P.rootSpanMem ℤ j := by
      apply scalarExtensionRootSpan_injective (P := P) (b := b)
      simpa only [map_neg, scalarExtensionRootSpan_root] using h
    exact congrArg Subtype.val hspan
  · exact scalarExtensionRoot_eq_neg (P := P) (b := b)

private lemma scalarExtension_linearIndependent_iff (i j : ι) :
    LinearIndependent RatAlgClosure ![
        (scalarExtension (P := P) (b := b)).root i,
        (scalarExtension (P := P) (b := b)).root j] ↔
      LinearIndependent R ![P.root i, P.root j] := by
  rw [RootPairing.IsReduced.linearIndependent_iff,
    RootPairing.IsReduced.linearIndependent_iff]
  change (i ≠ j ∧ scalarExtensionRoot (P := P) (b := b) i ≠
      -scalarExtensionRoot (P := P) (b := b) j) ↔
    (i ≠ j ∧ P.root i ≠ -P.root j)
  have hneg := scalarExtension_root_eq_neg_iff (P := P) (b := b) (i := i) (j := j)
  change (scalarExtensionRoot (P := P) (b := b) i =
      -scalarExtensionRoot (P := P) (b := b) j ↔
    P.root i = -P.root j) at hneg
  exact and_congr Iff.rfl (not_congr hneg)

private lemma scalarExtension_root_add_nsmul_mem_range_iff
    (i j : ι) (n : ℕ) :
    (scalarExtension (P := P) (b := b)).root j +
          n • (scalarExtension (P := P) (b := b)).root i ∈
        range (scalarExtension (P := P) (b := b)).root ↔
      P.root j + n • P.root i ∈ range P.root := by
  constructor <;> rintro ⟨k, hk⟩
  · exact ⟨k, scalarExtension_root_eq_add_nsmul_iff.mp hk⟩
  · exact ⟨k, scalarExtension_root_eq_add_nsmul_iff.mpr hk⟩

private lemma scalarExtension_root_sub_nsmul_mem_range_iff
    (i j : ι) (n : ℕ) :
    (scalarExtension (P := P) (b := b)).root j -
          n • (scalarExtension (P := P) (b := b)).root i ∈
        range (scalarExtension (P := P) (b := b)).root ↔
      P.root j - n • P.root i ∈ range P.root := by
  constructor <;> rintro ⟨k, hk⟩
  · exact ⟨k, scalarExtension_root_eq_sub_nsmul_iff.mp hk⟩
  · exact ⟨k, scalarExtension_root_eq_sub_nsmul_iff.mpr hk⟩

@[simp] private lemma scalarExtension_chainTopCoeff (i j : ι) :
    (scalarExtension (P := P) (b := b)).chainTopCoeff i j =
      P.chainTopCoeff i j := by
  let P' := scalarExtension (P := P) (b := b)
  by_cases hlin : LinearIndependent R ![P.root i, P.root j]
  · have hlin' : LinearIndependent RatAlgClosure ![
        (scalarExtension (P := P) (b := b)).root i,
        (scalarExtension (P := P) (b := b)).root j] :=
      (scalarExtension_linearIndependent_iff (P := P) (b := b) i j).2 hlin
    apply Nat.le_antisymm
    · apply (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff hlin).1
      rw [← scalarExtension_root_add_nsmul_mem_range_iff (P := P) (b := b)]
      exact (P'.root_add_nsmul_mem_range_iff_le_chainTopCoeff hlin').2 le_rfl
    · apply (P'.root_add_nsmul_mem_range_iff_le_chainTopCoeff hlin').1
      rw [scalarExtension_root_add_nsmul_mem_range_iff (P := P) (b := b)]
      exact (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff hlin).2 le_rfl
  · have hlin' : ¬LinearIndependent RatAlgClosure ![
        (scalarExtension (P := P) (b := b)).root i,
        (scalarExtension (P := P) (b := b)).root j] :=
      fun h => hlin ((scalarExtension_linearIndependent_iff
        (P := P) (b := b) i j).1 h)
    rw [P'.chainTopCoeff_of_not_linearIndependent hlin',
      P.chainTopCoeff_of_not_linearIndependent hlin]

@[simp] private lemma scalarExtension_chainBotCoeff (i j : ι) :
    (scalarExtension (P := P) (b := b)).chainBotCoeff i j =
      P.chainBotCoeff i j := by
  let P' := scalarExtension (P := P) (b := b)
  by_cases hlin : LinearIndependent R ![P.root i, P.root j]
  · have hlin' : LinearIndependent RatAlgClosure ![
        (scalarExtension (P := P) (b := b)).root i,
        (scalarExtension (P := P) (b := b)).root j] :=
      (scalarExtension_linearIndependent_iff (P := P) (b := b) i j).2 hlin
    apply Nat.le_antisymm
    · apply (P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff hlin).1
      rw [← scalarExtension_root_sub_nsmul_mem_range_iff (P := P) (b := b)]
      exact (P'.root_sub_nsmul_mem_range_iff_le_chainBotCoeff hlin').2 le_rfl
    · apply (P'.root_sub_nsmul_mem_range_iff_le_chainBotCoeff hlin').1
      rw [scalarExtension_root_sub_nsmul_mem_range_iff (P := P) (b := b)]
      exact (P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff hlin).2 le_rfl
  · have hlin' : ¬LinearIndependent RatAlgClosure ![
        (scalarExtension (P := P) (b := b)).root i,
        (scalarExtension (P := P) (b := b)).root j] :=
      fun h => hlin ((scalarExtension_linearIndependent_iff
        (P := P) (b := b) i j).1 h)
    rw [P'.chainBotCoeff_of_not_linearIndependent hlin',
      P.chainBotCoeff_of_not_linearIndependent hlin]

@[simp] private lemma scalarExtension_cartanMatrix (i j : b.support) :
    (scalarExtensionBase (P := P) (b := b)).cartanMatrix i j =
      b.cartanMatrix i j := by
  change (scalarExtension (P := P) (b := b)).pairingIn ℤ i j =
    P.pairingIn ℤ i j
  exact scalarExtension_pairingIn (P := P) (b := b) i j

set_option backward.isDefEq.respectTransparency false

@[simp] public lemma scalarExtension_eMatrix (i : b.support) :
    eMatrix (P := scalarExtension (P := P) (b := b))
        (b := scalarExtensionBase (P := P) (b := b)) i =
      eMatrix (P := P) (b := b) i := by
  classical
  ext (row | row) (column | column) <;>
    simp [eMatrix, scalarExtension_cartanMatrix, scalarExtension_chainBotCoeff,
      scalarExtension_root_eq_add_iff]

@[simp] private lemma scalarExtension_eDividedPower (i : b.support) (n : ℕ) :
    eDividedPower (P := scalarExtension (P := P) (b := b))
        (b := scalarExtensionBase (P := P) (b := b)) i n =
      eDividedPower (P := P) (b := b) i n := by
  unfold scalarExtensionBase
  rcases n with _ | _ | n
  · rfl
  · exact scalarExtension_eMatrix (P := P) (b := b) i
  · ext (row | row) (column | column) <;>
      simp [eDividedPower, scalarExtension_chainBotCoeff]
    rw [scalarExtension_root_eq_add_nsmul_iff (P := P) (b := b)]

@[simp] private lemma scalarExtension_omegaMatrix :
    omegaMatrix (P := scalarExtension (P := P) (b := b))
        (b := scalarExtensionBase (P := P) (b := b)) =
      omegaMatrix (P := P) (b := b) := by
  letI := P.indexNeg
  unfold scalarExtensionBase
  ext (row | row) (column | column) <;>
    simp [omegaMatrix, Matrix.one_apply]

@[simp] private lemma scalarExtension_fDividedPower (i : b.support) (n : ℕ) :
    fDividedPower (P := scalarExtension (P := P) (b := b))
        (b := scalarExtensionBase (P := P) (b := b)) i n =
      fDividedPower (P := P) (b := b) i n := by
  unfold fDividedPower
  rw [scalarExtension_omegaMatrix,
    scalarExtension_eDividedPower]

@[simp] private lemma scalarExtension_eUnipotent (i : b.support) (t : ℤ) :
    eUnipotent (P := scalarExtension (P := P) (b := b))
        (b := scalarExtensionBase (P := P) (b := b)) i t =
      eUnipotent (P := P) (b := b) i t := by
  unfold eUnipotent
  rw [scalarExtension_eDividedPower,
    scalarExtension_eDividedPower, scalarExtension_eDividedPower]

@[simp] private lemma scalarExtension_fUnipotent (i : b.support) (t : ℤ) :
    fUnipotent (P := scalarExtension (P := P) (b := b))
        (b := scalarExtensionBase (P := P) (b := b)) i t =
      fUnipotent (P := P) (b := b) i t := by
  unfold fUnipotent
  rw [scalarExtension_fDividedPower,
    scalarExtension_fDividedPower, scalarExtension_fDividedPower]

@[simp] private lemma scalarExtension_titsLift (i : b.support) :
    titsLift (P := scalarExtension (P := P) (b := b))
        (b := scalarExtensionBase (P := P) (b := b)) i =
      titsLift (P := P) (b := b) i := by
  unfold titsLift
  rw [scalarExtension_eUnipotent, scalarExtension_fUnipotent]

@[simp] private lemma scalarExtension_titsLiftInv (i : b.support) :
    titsLiftInv (P := scalarExtension (P := P) (b := b))
        (b := scalarExtensionBase (P := P) (b := b)) i =
      titsLiftInv (P := P) (b := b) i := by
  unfold titsLiftInv
  rw [scalarExtension_eUnipotent, scalarExtension_fUnipotent]

@[simp] private lemma scalarExtension_titsWord (word : List b.support) :
    titsWord (P := scalarExtension (P := P) (b := b))
        (b := scalarExtensionBase (P := P) (b := b)) word =
      titsWord (P := P) (b := b) word := by
  induction word with
  | nil => rfl
  | cons i word ih =>
      change titsLift (P := scalarExtension (P := P) (b := b))
          (b := scalarExtensionBase (P := P) (b := b)) i *
            titsWord (P := scalarExtension (P := P) (b := b))
              (b := scalarExtensionBase (P := P) (b := b)) word =
        titsLift (P := P) (b := b) i * titsWord (P := P) (b := b) word
      rw [scalarExtension_titsLift, ih]

@[simp] private lemma scalarExtension_titsWordInv (word : List b.support) :
    titsWordInv (P := scalarExtension (P := P) (b := b))
        (b := scalarExtensionBase (P := P) (b := b)) word =
      titsWordInv (P := P) (b := b) word := by
  induction word with
  | nil => rfl
  | cons i word ih =>
      change titsWordInv (P := scalarExtension (P := P) (b := b))
          (b := scalarExtensionBase (P := P) (b := b)) word *
            titsLiftInv (P := scalarExtension (P := P) (b := b))
              (b := scalarExtensionBase (P := P) (b := b)) i =
        titsWordInv (P := P) (b := b) word * titsLiftInv (P := P) (b := b) i
      rw [scalarExtension_titsLiftInv, ih]

@[simp] public lemma scalarExtension_titsConjugate
    (word : List b.support)
    (A : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ) :
    titsConjugate (P := scalarExtension (P := P) (b := b))
        (b := scalarExtensionBase (P := P) (b := b)) word A =
      titsConjugate (P := P) (b := b) word A := by
  unfold titsConjugate
  rw [scalarExtension_titsWord,
    scalarExtension_titsWordInv]

@[simp] public lemma scalarExtension_reflectionWord
    (word : List b.support) (i : ι) :
    reflectionWord (P := scalarExtension (P := P) (b := b))
        (b := scalarExtensionBase (P := P) (b := b)) word i =
      reflectionWord (P := P) (b := b) word i := by
  induction word with
  | nil => rfl
  | cons j word ih =>
      change (scalarExtension (P := P) (b := b)).reflectionPerm j
          (reflectionWord (P := scalarExtension (P := P) (b := b))
            (b := scalarExtensionBase (P := P) (b := b)) word i) =
        P.reflectionPerm j (reflectionWord (P := P) (b := b) word i)
      rw [ih]
      rfl

end
end RootPairing.IntegralGeckConstruction
