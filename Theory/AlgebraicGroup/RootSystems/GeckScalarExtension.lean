module

public import Theory.AlgebraicGroup.RootSystems.IntegralTitsCoherence
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Basis
import Mathlib.LinearAlgebra.Matrix.Dual

/-!
# Scalar extension for the integral Geck model

This module constructs, from a finite irreducible reduced crystallographic root system and a
base, a root system over an algebraic closure of `ℚ` with the same integral root coordinates.
Roots are expressed in the simple-root basis and coroots by their simple-root pairings, so their
dot product recovers the original Cartan pairing.  The construction proves the root-system,
reducedness, and irreducibility instances needed by Geck's semisimplicity theorem.

The construction is a coefficient-field bridge for the integral Tits model.  It uses only the
integral coordinate data exposed by `IntegralTitsCoherence` and Mathlib's Geck root-system API;
it does not use route coherence or component decomposition.
-/

namespace RootPairing.IntegralGeckConstruction

open Function Matrix Set Submodule

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

public abbrev RatAlgClosure := AlgebraicClosure ℚ

local instance : Algebra ℤ RatAlgClosure := Ring.toIntAlgebra RatAlgClosure

variable {ι R M N : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsCrystallographic]
  [P.IsReduced] [P.IsIrreducible]
  {b : P.Base} [Fintype ι] [DecidableEq ι]

/-- Integral simple-root coordinates, mapped to an algebraic closure of `ℚ`. -/
@[expose] public def scalarExtensionRoot (i : ι) : b.support → RatAlgClosure :=
  fun k => algebraMap ℤ RatAlgClosure (b.toWeightBasisInt.repr (P.rootSpanMem ℤ i) k)

/-- Integral Cartan coordinates of a coroot, mapped to an algebraic closure of `ℚ`. -/
@[expose] public def scalarExtensionCoroot (i : ι) : b.support → RatAlgClosure :=
  fun k => algebraMap ℤ RatAlgClosure (P.pairingIn ℤ k i)

private lemma pairingIn_flip_int (i j : ι) :
    P.flip.pairingIn ℤ i j = P.pairingIn ℤ j i := by
  apply FaithfulSMul.algebraMap_injective ℤ R
  simp only [P.flip.algebraMap_pairingIn, P.algebraMap_pairingIn,
    RootPairing.pairing_flip]

public lemma scalarExtensionRoot_injective :
    Injective (scalarExtensionRoot (P := P) (b := b)) := by
  intro i j hij
  apply P.root.injective
  have hrepr : b.toWeightBasisInt.repr (P.rootSpanMem ℤ i) =
      b.toWeightBasisInt.repr (P.rootSpanMem ℤ j) := by
    ext k
    apply FaithfulSMul.algebraMap_injective ℤ RatAlgClosure
    exact congrFun hij k
  exact congrArg Subtype.val (b.toWeightBasisInt.repr.injective hrepr)

public lemma scalarExtensionCoroot_injective :
    Injective (scalarExtensionCoroot (P := P) (b := b)) := by
  intro i j hij
  apply b.flip.injective_pairingIn
  funext k
  change P.flip.pairingIn ℤ i (k : ι) = P.flip.pairingIn ℤ j (k : ι)
  rw [pairingIn_flip_int, pairingIn_flip_int]
  apply FaithfulSMul.algebraMap_injective ℤ RatAlgClosure
  exact congrFun hij (show b.support from k)

@[simp] public lemma scalarExtensionRoot_simple (i : b.support) :
    scalarExtensionRoot (P := P) (b := b) i = Pi.single i 1 := by
  have hi : P.rootSpanMem ℤ (i : ι) = b.toWeightBasisInt i := by
    ext
    exact b.coe_toWeightBasisInt_apply i |>.symm
  ext k
  rw [scalarExtensionRoot, hi, b.toWeightBasisInt.repr_self]
  by_cases hik : i = k
  · subst k
    simp
  · simp [hik, Ne.symm hik]

public lemma scalarExtension_pairing (i j : ι) :
    dotProduct (scalarExtensionRoot (P := P) (b := b) i)
        (scalarExtensionCoroot (P := P) (b := b) j) =
      algebraMap ℤ RatAlgClosure (P.pairingIn ℤ i j) := by
  rw [dotProduct]
  have h := congrArg (P.coroot'In ℤ j)
    (b.toWeightBasisInt.sum_repr (P.rootSpanMem ℤ i))
  have hs : ∑ k : b.support,
      b.toWeightBasisInt.repr (P.rootSpanMem ℤ i) k * P.pairingIn ℤ k j =
        P.pairingIn ℤ i j := by
    rw [map_sum] at h
    simp_rw [map_smul] at h
    simp_rw [show ∀ k : b.support,
        b.toWeightBasisInt k = P.rootSpanMem ℤ (k : ι) by
      intro k
      apply Subtype.ext
      exact b.coe_toWeightBasisInt_apply k] at h
    simpa only [coroot'In_rootSpanMem_eq_pairingIn, smul_eq_mul] using h
  calc
    _ = algebraMap ℤ RatAlgClosure (∑ k : b.support,
        b.toWeightBasisInt.repr (P.rootSpanMem ℤ i) k * P.pairingIn ℤ k j) := by
      simp [scalarExtensionRoot, scalarExtensionCoroot]
    _ = _ := congrArg (algebraMap ℤ RatAlgClosure) hs

public lemma scalarExtensionRoot_reflection (i j : ι) :
    scalarExtensionRoot (P := P) (b := b) j -
        algebraMap ℤ RatAlgClosure (P.pairingIn ℤ j i) •
          scalarExtensionRoot (P := P) (b := b) i =
      scalarExtensionRoot (P := P) (b := b) (P.reflectionPerm i j) := by
  have hroot : P.rootSpanMem ℤ j - P.pairingIn ℤ j i • P.rootSpanMem ℤ i =
      P.rootSpanMem ℤ (P.reflectionPerm i j) := by
    apply Subtype.ext
    change (P.rootSpan ℤ).subtype
      (P.rootSpanMem ℤ j - P.pairingIn ℤ j i • P.rootSpanMem ℤ i) = _
    rw [map_sub, map_zsmul]
    change P.root j - P.pairingIn ℤ j i • P.root i = P.root (P.reflectionPerm i j)
    simpa only [P.root_coroot_eq_pairing, ← P.algebraMap_pairingIn ℤ,
      algebraMap_smul] using
      P.reflectionPerm_root i j
  have hrepr := congrArg b.toWeightBasisInt.repr hroot
  rw [map_sub, map_zsmul] at hrepr
  ext k
  have hk := congrFun (congrArg DFunLike.coe hrepr) k
  simpa [scalarExtensionRoot, sub_eq_add_neg, map_mul] using
    congrArg (algebraMap ℤ RatAlgClosure) hk

public lemma scalarExtensionCoroot_reflection (i j : ι) :
    scalarExtensionCoroot (P := P) (b := b) j -
        algebraMap ℤ RatAlgClosure (P.pairingIn ℤ i j) •
          scalarExtensionCoroot (P := P) (b := b) i =
      scalarExtensionCoroot (P := P) (b := b) (P.reflectionPerm i j) := by
  ext k
  change algebraMap ℤ RatAlgClosure (P.pairingIn ℤ k j) -
      algebraMap ℤ RatAlgClosure (P.pairingIn ℤ i j) *
        algebraMap ℤ RatAlgClosure (P.pairingIn ℤ k i) =
    algebraMap ℤ RatAlgClosure (P.pairingIn ℤ k (P.reflectionPerm i j))
  have hint : P.pairingIn ℤ (k : ι) j -
      P.pairingIn ℤ i j * P.pairingIn ℤ (k : ι) i =
    P.pairingIn ℤ (k : ι) (P.reflectionPerm i j) := by
    apply FaithfulSMul.algebraMap_injective ℤ R
    rw [map_sub, map_mul]
    have hcoroot : P.coroot j - P.pairingIn ℤ i j • P.coroot i =
        P.coroot (P.reflectionPerm i j) := by
      simpa only [P.root_coroot_eq_pairing, ← P.algebraMap_pairingIn ℤ,
        algebraMap_smul] using P.reflectionPerm_coroot i j
    have h := congrArg (P.root' (k : ι)) hcoroot
    rw [map_sub, map_zsmul] at h
    have h' : P.pairing (k : ι) j - (P.pairingIn ℤ i j : R) *
        P.pairing (k : ι) i = P.pairing (k : ι) (P.reflectionPerm i j) := by
      simpa only [P.root'_coroot_eq_pairing, zsmul_eq_mul] using h
    have intCast_eq (n : ℤ) : (n : R) = algebraMap ℤ R n := rfl
    simp_rw [intCast_eq] at h'
    simpa only [← P.algebraMap_pairingIn ℤ] using h'
  simpa only [map_sub, map_mul] using congrArg (algebraMap ℤ RatAlgClosure) hint

/-- Coordinate scalar extension of a crystallographic root system to `AlgebraicClosure ℚ`. -/
@[expose] public def scalarExtension :
    RootPairing ι RatAlgClosure (b.support → RatAlgClosure) (b.support → RatAlgClosure) where
  toLinearMap := dotProductBilin RatAlgClosure RatAlgClosure
  isPerfPair_toLinearMap := by
    change (dotProductEquiv RatAlgClosure b.support).toLinearMap.IsPerfPair
    infer_instance
  root := ⟨scalarExtensionRoot, scalarExtensionRoot_injective⟩
  coroot := ⟨scalarExtensionCoroot, scalarExtensionCoroot_injective⟩
  root_coroot_two i := by
    change dotProduct (scalarExtensionRoot (P := P) (b := b) i)
      (scalarExtensionCoroot (P := P) (b := b) i) = 2
    rw [scalarExtension_pairing,
      P.pairingIn_same, map_ofNat]
  reflectionPerm := P.reflectionPerm
  reflectionPerm_root i j := by
    change scalarExtensionRoot (P := P) (b := b) j -
      dotProduct (scalarExtensionRoot (P := P) (b := b) j)
        (scalarExtensionCoroot (P := P) (b := b) i) •
          scalarExtensionRoot (P := P) (b := b) i =
        scalarExtensionRoot (P := P) (b := b) (P.reflectionPerm i j)
    simpa only [scalarExtension_pairing] using
      scalarExtensionRoot_reflection (P := P) (b := b) i j
  reflectionPerm_coroot i j := by
    change scalarExtensionCoroot (P := P) (b := b) j -
      dotProduct (scalarExtensionRoot (P := P) (b := b) i)
        (scalarExtensionCoroot (P := P) (b := b) j) •
          scalarExtensionCoroot (P := P) (b := b) i =
        scalarExtensionCoroot (P := P) (b := b) (P.reflectionPerm i j)
    simpa only [scalarExtension_pairing] using
      scalarExtensionCoroot_reflection (P := P) (b := b) i j

private instance scalarExtensionIsCrystallographicPrivate :
    (scalarExtension (P := P) (b := b)).IsCrystallographic := by
  constructor
  intro i j
  exact ⟨P.pairingIn ℤ i j, by
    change algebraMap ℤ RatAlgClosure (P.pairingIn ℤ i j) =
      dotProduct (scalarExtensionRoot (P := P) (b := b) i)
        (scalarExtensionCoroot (P := P) (b := b) j)
    exact (scalarExtension_pairing (P := P) (b := b) i j).symm⟩

@[simp] private lemma scalarExtension_pairingIn (i j : ι) :
    (scalarExtension (P := P) (b := b)).pairingIn ℤ i j = P.pairingIn ℤ i j := by
  apply FaithfulSMul.algebraMap_injective ℤ RatAlgClosure
  rw [(scalarExtension (P := P) (b := b)).algebraMap_pairingIn ℤ]
  change dotProduct (scalarExtensionRoot (P := P) (b := b) i)
      (scalarExtensionCoroot (P := P) (b := b) j) =
    algebraMap ℤ RatAlgClosure (P.pairingIn ℤ i j)
  exact scalarExtension_pairing (P := P) (b := b) i j

public lemma scalarExtensionCoroot_linearIndependent :
    LinearIndependent RatAlgClosure
      (fun i : b.support => scalarExtensionCoroot (P := P) (b := b) i) := by
  let C : Matrix b.support b.support RatAlgClosure :=
    b.cartanMatrix.map (algebraMap ℤ RatAlgClosure)
  have hdetZ : b.cartanMatrix.det ≠ 0 :=
    (Matrix.nondegenerate_iff_det_ne_zero.mp b.cartanMatrix_nondegenerate)
  have hdet : C.det ≠ 0 := by
    calc
      C.det = algebraMap ℤ RatAlgClosure b.cartanMatrix.det := by
        exact (RingHom.map_det (algebraMap ℤ RatAlgClosure) b.cartanMatrix).symm
      _ ≠ 0 := by
        intro hzero
        apply hdetZ
        apply FaithfulSMul.algebraMap_injective ℤ RatAlgClosure
        simpa only [map_zero] using hzero
  have hli := Matrix.linearIndependent_cols_of_det_ne_zero hdet
  change LinearIndependent RatAlgClosure C.col
  exact hli

private instance scalarExtensionIsRootSystemPrivate :
    (scalarExtension (P := P) (b := b)).IsRootSystem := by
  constructor
  ·
    rw [eq_top_iff]
    intro x hx
    have htop := (Pi.basisFun RatAlgClosure b.support).span_eq
    rw [← htop] at hx
    apply (span_mono ?_) hx
    rintro y ⟨i, rfl⟩
    rw [Pi.basisFun_apply, ← scalarExtensionRoot_simple (P := P) (b := b) i]
    exact ⟨(i : ι), rfl⟩
  ·
    rw [eq_top_iff]
    intro x hx
    have htop := scalarExtensionCoroot_linearIndependent (P := P) (b := b)
      |>.span_eq_top_of_card_eq_finrank' (by simp)
    rw [← htop] at hx
    apply (span_mono ?_) hx
    rintro y ⟨i, rfl⟩
    exact ⟨(i : ι), rfl⟩

public lemma scalarExtensionRoot_eq_sum {i : ι} (f : ι → ℕ)
    (h : P.root i = ∑ j ∈ b.support, f j • P.root j) :
    scalarExtensionRoot (P := P) (b := b) i =
      ∑ j ∈ b.support, f j • scalarExtensionRoot (P := P) (b := b) j := by
  have hspan : P.rootSpanMem ℤ i =
      ∑ j ∈ b.support, f j • P.rootSpanMem ℤ j := by
    apply Subtype.ext
    simpa using h
  have hrepr := congrArg b.toWeightBasisInt.repr hspan
  rw [map_sum] at hrepr
  simp_rw [map_nsmul] at hrepr
  ext k
  have hk := congrFun (congrArg DFunLike.coe hrepr) k
  simpa [scalarExtensionRoot] using congrArg (algebraMap ℤ RatAlgClosure) hk

public lemma scalarExtensionCoroot_eq_sum {i : ι} (f : ι → ℕ)
    (h : P.coroot i = ∑ j ∈ b.support, f j • P.coroot j) :
    scalarExtensionCoroot (P := P) (b := b) i =
      ∑ j ∈ b.support, f j • scalarExtensionCoroot (P := P) (b := b) j := by
  ext k
  simp only [scalarExtensionCoroot, Finset.sum_apply]
  simp_rw [show ∀ (n : ℕ) (v : b.support → RatAlgClosure) (l : b.support),
      (n • v) l = n • v l by intros; rfl]
  change algebraMap ℤ RatAlgClosure (P.pairingIn ℤ (k : ι) i) =
    ∑ j ∈ b.support, f j •
      algebraMap ℤ RatAlgClosure (P.pairingIn ℤ (k : ι) j)
  have hk := congrArg (P.root' (k : ι)) h
  have hint : P.pairingIn ℤ (k : ι) i =
      ∑ j ∈ b.support, f j • P.pairingIn ℤ (k : ι) j := by
    apply FaithfulSMul.algebraMap_injective ℤ R
    simpa [P.root_coroot_eq_pairing, ← P.algebraMap_pairingIn ℤ, map_sum,
      algebraMap_smul] using hk
  simpa [map_sum] using congrArg (algebraMap ℤ RatAlgClosure) hint

public lemma scalarExtensionRoot_eq_neg {i j : ι} (h : P.root i = -P.root j) :
    scalarExtensionRoot (P := P) (b := b) i =
      -scalarExtensionRoot (P := P) (b := b) j := by
  have hspan : P.rootSpanMem ℤ i = -P.rootSpanMem ℤ j := by
    apply Subtype.ext
    change (P.rootSpan ℤ).subtype (P.rootSpanMem ℤ i) =
      (P.rootSpan ℤ).subtype (-P.rootSpanMem ℤ j)
    rw [map_neg]
    exact h
  have hrepr := congrArg b.toWeightBasisInt.repr hspan
  rw [map_neg] at hrepr
  ext k
  have hk := congrFun (congrArg DFunLike.coe hrepr) k
  simpa [scalarExtensionRoot] using congrArg (algebraMap ℤ RatAlgClosure) hk

public lemma scalarExtensionCoroot_eq_neg {i j : ι} (h : P.coroot i = -P.coroot j) :
    scalarExtensionCoroot (P := P) (b := b) i =
      -scalarExtensionCoroot (P := P) (b := b) j := by
  ext k
  have hk := congrArg (P.root' (k : ι)) h
  have hint : P.pairingIn ℤ (k : ι) i = -P.pairingIn ℤ (k : ι) j := by
    apply FaithfulSMul.algebraMap_injective ℤ R
    simpa [P.root_coroot_eq_pairing, ← P.algebraMap_pairingIn ℤ] using hk
  simpa [scalarExtensionCoroot] using congrArg (algebraMap ℤ RatAlgClosure) hint

@[expose] public noncomputable def scalarExtensionBase :
    (scalarExtension (P := P) (b := b)).Base where
  support := b.support
  linearIndepOn_root := by
    rw [← linearIndependent_comp_subtype_iff]
    change LinearIndependent RatAlgClosure
      (fun i : {i // i ∈ (b.support : Set ι)} =>
        scalarExtensionRoot (P := P) (b := b) (i : ι))
    let f : {i // i ∈ (b.support : Set ι)} → b.support :=
      fun i => ⟨i, i.property⟩
    have hli := (Pi.linearIndependent_single_one b.support RatAlgClosure).comp f
      (fun _ _ h => Subtype.ext (congrArg Subtype.val h))
    have heq : (fun i : {i // i ∈ (b.support : Set ι)} =>
        scalarExtensionRoot (P := P) (b := b) (i : ι)) =
        (fun i : b.support => Pi.single i (1 : RatAlgClosure)) ∘ f := by
      funext i
      exact scalarExtensionRoot_simple (P := P) (b := b) (f i)
    rw [heq]
    exact hli
  linearIndepOn_coroot := by
    rw [← linearIndependent_comp_subtype_iff]
    change LinearIndependent RatAlgClosure
      (fun i : {i // i ∈ (b.support : Set ι)} =>
        scalarExtensionCoroot (P := P) (b := b) (i : ι))
    let f : {i // i ∈ (b.support : Set ι)} → b.support :=
      fun i => ⟨i, i.property⟩
    exact (scalarExtensionCoroot_linearIndependent (P := P) (b := b)).comp f
      (fun _ _ h => Subtype.ext (congrArg Subtype.val h))
  root_mem_or_neg_mem i := by
    rcases b.exists_root_eq_sum_nat_or_neg i with ⟨f, -, h | h⟩
    · left
      change scalarExtensionRoot (P := P) (b := b) i ∈
        AddSubmonoid.closure
          (scalarExtensionRoot (P := P) (b := b) '' (b.support : Set ι))
      rw [scalarExtensionRoot_eq_sum (P := P) (b := b) f h]
      exact AddSubmonoid.sum_mem _ fun j hj => by
        have hj' : scalarExtensionRoot (P := P) (b := b) (j : ι) ∈
            scalarExtensionRoot (P := P) (b := b) '' (b.support : Set ι) :=
          ⟨(j : ι), by simpa using hj, rfl⟩
        exact AddSubmonoid.nsmul_mem _ (AddSubmonoid.subset_closure hj') _

    · right
      change -scalarExtensionRoot (P := P) (b := b) i ∈
        AddSubmonoid.closure
          (scalarExtensionRoot (P := P) (b := b) '' (b.support : Set ι))
      letI := P.indexNeg
      have h' : -P.root i = ∑ j ∈ b.support, f j • P.root j := by
        simpa only [neg_neg] using congrArg Neg.neg h
      have hneg : scalarExtensionRoot (P := P) (b := b) (-i) =
          -scalarExtensionRoot (P := P) (b := b) i :=
        scalarExtensionRoot_eq_neg (P := P) (b := b) (by simp)
      rw [← hneg, scalarExtensionRoot_eq_sum (P := P) (b := b) f (by simpa using h')]
      exact AddSubmonoid.sum_mem _ fun j hj => by
        have hj' : scalarExtensionRoot (P := P) (b := b) (j : ι) ∈
            scalarExtensionRoot (P := P) (b := b) '' (b.support : Set ι) :=
          ⟨(j : ι), by simpa using hj, rfl⟩
        exact AddSubmonoid.nsmul_mem _ (AddSubmonoid.subset_closure hj') _
  coroot_mem_or_neg_mem i := by
    rcases b.flip.exists_root_eq_sum_nat_or_neg i with ⟨f, -, h | h⟩
    · left
      change scalarExtensionCoroot (P := P) (b := b) i ∈
        AddSubmonoid.closure
          (scalarExtensionCoroot (P := P) (b := b) '' (b.support : Set ι))
      rw [scalarExtensionCoroot_eq_sum (P := P) (b := b) f h]
      exact AddSubmonoid.sum_mem _ fun j hj => by
        have hj' : scalarExtensionCoroot (P := P) (b := b) (j : ι) ∈
            scalarExtensionCoroot (P := P) (b := b) '' (b.support : Set ι) :=
          ⟨(j : ι), by simpa using hj, rfl⟩
        exact AddSubmonoid.nsmul_mem _ (AddSubmonoid.subset_closure hj') _
    · right
      change -scalarExtensionCoroot (P := P) (b := b) i ∈
        AddSubmonoid.closure
          (scalarExtensionCoroot (P := P) (b := b) '' (b.support : Set ι))
      letI := P.indexNeg
      have h' : -P.coroot i = ∑ j ∈ b.support, f j • P.coroot j := by
        simpa only [RootPairing.Base.flip, RootPairing.flip, neg_neg] using congrArg Neg.neg h
      have hneg : scalarExtensionCoroot (P := P) (b := b) (-i) =
          -scalarExtensionCoroot (P := P) (b := b) i :=
        scalarExtensionCoroot_eq_neg (P := P) (b := b) (by simp)
      rw [← hneg, scalarExtensionCoroot_eq_sum (P := P) (b := b) f (by simpa using h')]
      exact AddSubmonoid.sum_mem _ fun j hj => by
        have hj' : scalarExtensionCoroot (P := P) (b := b) (j : ι) ∈
            scalarExtensionCoroot (P := P) (b := b) '' (b.support : Set ι) :=
          ⟨(j : ι), by simpa using hj, rfl⟩
        exact AddSubmonoid.nsmul_mem _ (AddSubmonoid.subset_closure hj') _

private instance scalarExtensionIsReducedPrivate :
    (scalarExtension (P := P) (b := b)).IsReduced := by
  rw [RootPairing.isReduced_iff']
  intro i j hij hdep
  have hcox : (scalarExtension (P := P) (b := b)).coxeterWeightIn ℤ i j = 4 :=
    ((scalarExtension (P := P) (b := b)).coxeterWeightIn_eq_four_iff_not_linearIndependent
      ℤ).2 hdep
  have hcoxP : P.coxeterWeightIn ℤ i j = 4 := by
    simpa only [RootPairing.coxeterWeightIn, scalarExtension_pairingIn] using hcox
  have hdepP : ¬LinearIndependent R ![P.root i, P.root j] :=
    (P.coxeterWeightIn_eq_four_iff_not_linearIndependent ℤ).1 hcoxP
  rcases IsReduced.eq_or_eq_neg (P := P) i j hdepP with heq | hneg
  · exact False.elim (hij (P.root.injective heq))
  · change scalarExtensionRoot (P := P) (b := b) i =
      -scalarExtensionRoot (P := P) (b := b) j
    exact scalarExtensionRoot_eq_neg (P := P) (b := b) hneg

public lemma exists_simple_coroot_pairing_ne
    {x : b.support → RatAlgClosure} (hx : x ≠ 0) :
    ∃ i : b.support,
      dotProduct x (scalarExtensionCoroot (P := P) (b := b) i) ≠ 0 := by
  by_contra hnone
  push Not at hnone
  have hzero : ∀ y : b.support → RatAlgClosure, dotProduct x y = 0 := by
    intro y
    have hy : y ∈ span RatAlgClosure
        (range (fun i : b.support => scalarExtensionCoroot (P := P) (b := b) i)) := by
      rw [scalarExtensionCoroot_linearIndependent (P := P) (b := b)
        |>.span_eq_top_of_card_eq_finrank' (by simp)]
      trivial
    induction hy using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨i, rfl⟩ := hy
        exact hnone i
    | zero => simp [dotProduct]
    | add y z _ _ hy hz => rw [dotProduct_add, hy, hz, add_zero]
    | smul a y _ hy => rw [dotProduct_smul, hy, smul_zero]
  apply hx
  funext i
  have hi := hzero (Pi.single i 1)
  simpa [dotProduct, Pi.single_apply] using hi

public lemma root_mem_of_pairing_mem
    (q : Submodule RatAlgClosure (b.support → RatAlgClosure))
    (hstable : ∀ i, q ∈ Module.End.invtSubmodule
      ((scalarExtension (P := P) (b := b)).reflection i))
    {x : b.support → RatAlgClosure} (hx : x ∈ q) {i : ι}
    (hi : (scalarExtension (P := P) (b := b)).coroot' i x ≠ 0) :
    (scalarExtension (P := P) (b := b)).root i ∈ q := by
  have href := hstable i hx
  have hsmul := q.sub_mem hx href
  have hsmul' :
      (scalarExtension (P := P) (b := b)).coroot' i x •
        (scalarExtension (P := P) (b := b)).root i ∈ q := by
    have heq : x - (scalarExtension (P := P) (b := b)).reflection i x =
        (scalarExtension (P := P) (b := b)).coroot' i x •
          (scalarExtension (P := P) (b := b)).root i := by
      rw [RootPairing.reflection_apply]
      abel
    rwa [← heq]
  have hinv := q.smul_mem ((scalarExtension (P := P) (b := b)).coroot' i x)⁻¹ hsmul'
  simpa only [smul_smul, inv_mul_cancel₀ hi, one_smul] using hinv

public lemma originalIndex_nonempty (P : RootPairing ι R M N)
    [P.IsRootSystem] [P.IsIrreducible] : Nonempty ι := by
  letI : Nontrivial M := IsIrreducible.nontrivial P
  by_contra h
  haveI : IsEmpty ι := not_nonempty_iff.mp h
  have htop := RootPairing.IsRootSystem.span_root_eq_top (P := P)
  have hrange : range P.root = (∅ : Set M) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact isEmptyElim i
    · simp
  rw [hrange, span_empty] at htop
  exact bot_ne_top htop

private instance scalarExtensionIsIrreduciblePrivate :
    (scalarExtension (P := P) (b := b)).IsIrreducible := by
  let P' := scalarExtension (P := P) (b := b)
  let b' := scalarExtensionBase (P := P) (b := b)
  letI : Nonempty ι := originalIndex_nonempty (P := P)
  letI : Nonempty b.support := b.support_nonempty.to_subtype
  apply RootPairing.IsIrreducible.mk' P'
  intro q hstable hq
  obtain ⟨x, hx, hx0⟩ := q.ne_bot_iff.mp hq
  have hsome : ∃ r : ι, P'.coroot' r x ≠ 0 := by
    by_contra hnone
    push Not at hnone
    exact hx0 (P'.eq_zero_iff_forall_coroot'_eq_zero.2 hnone)
  obtain ⟨r, hr⟩ := hsome
  have hrq : P'.root r ∈ q :=
    root_mem_of_pairing_mem (P := P) (b := b) q hstable hx hr
  obtain ⟨i, hi⟩ := exists_simple_coroot_pairing_ne (P := P) (b := b) (P'.ne_zero r)
  have hi' : P'.coroot' (i : ι) (P'.root r) ≠ 0 := by
    simpa [P', scalarExtension] using hi
  have hrooti : P'.root (i : ι) ∈ q :=
    root_mem_of_pairing_mem (P := P) (b := b) q hstable hrq hi'
  have hall : ∀ j : b.support, P'.root (j : ι) ∈ q := by
    intro j
    apply b.induction_on_cartanMatrix
      (p := fun k : b.support => P'.root (k : ι) ∈ q) hrooti
    intro k l hk hcartan
    have hpair : P'.coroot' (l : ι) (P'.root (k : ι)) ≠ 0 := by
      change P'.pairing (k : ι) (l : ι) ≠ 0
      rw [← P'.algebraMap_pairingIn ℤ, scalarExtension_pairingIn]
      intro hzero
      have hmap : algebraMap ℤ RatAlgClosure (P.pairingIn ℤ (k : ι) (l : ι)) =
          algebraMap ℤ RatAlgClosure 0 := by
        simpa only [map_zero] using hzero
      have hz := FaithfulSMul.algebraMap_injective ℤ RatAlgClosure hmap
      exact hcartan (by
        rwa [← b.cartanMatrix_apply_eq_zero_iff_symm])
    exact root_mem_of_pairing_mem (P := P) (b := b) q hstable hk hpair
  rw [eq_top_iff]
  intro x hx
  have hxspan : x ∈ span RatAlgClosure
      (range (fun i : b.support => P'.root (i : ι))) := by
    have hbasis : (fun i : b.support => Pi.single i (1 : RatAlgClosure)) =
        (Pi.basisFun RatAlgClosure b.support : b.support → b.support → RatAlgClosure) := by
      funext i
      exact (Pi.basisFun_apply RatAlgClosure b.support i).symm
    have hle : span RatAlgClosure
        (range (fun i : b.support => Pi.single i (1 : RatAlgClosure))) ≤
        span RatAlgClosure (range (fun i : b.support => P'.root (i : ι))) := by
      apply span_mono
      rintro y ⟨i, rfl⟩
      change Pi.single i 1 ∈ _
      rw [← scalarExtensionRoot_simple (P := P) (b := b) i]
      exact ⟨i, rfl⟩
    apply hle
    rw [hbasis, (Pi.basisFun RatAlgClosure b.support).span_eq]
    trivial
  exact span_le.2 (by rintro - ⟨j, rfl⟩; exact hall j) hxspan

@[instance] public theorem scalarExtensionIsCrystallographic :
    (scalarExtension (P := P) (b := b)).IsCrystallographic :=
  scalarExtensionIsCrystallographicPrivate (P := P) (b := b)

@[instance] public theorem scalarExtensionIsRootSystem :
    (scalarExtension (P := P) (b := b)).IsRootSystem :=
  scalarExtensionIsRootSystemPrivate (P := P) (b := b)

@[instance] public theorem scalarExtensionIsReduced :
    (scalarExtension (P := P) (b := b)).IsReduced :=
  scalarExtensionIsReducedPrivate (P := P) (b := b)

@[instance] public theorem scalarExtensionIsIrreducible :
    (scalarExtension (P := P) (b := b)).IsIrreducible :=
  scalarExtensionIsIrreduciblePrivate (P := P) (b := b)

end
end RootPairing.IntegralGeckConstruction
