module

public import Theory.AlgebraicGroup.RootSystems.GeckTitsCartanAction
import Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Basis

/-!
# Root weights of integral Tits conjugates

This module identifies the Cartan weight of a simple integral Geck root operator after
conjugation by a Tits word.  The weight is the root obtained by the matching reflection word.
Together with `GeckTitsExponential`, this places mapped Tits conjugates in the correct Geck root
space.
-/

namespace RootPairing.IntegralGeckConstruction

open Matrix

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

variable {ι R M N : Type*} [Field R] [CharZero R] [IsAlgClosed R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsCrystallographic]
  [P.IsReduced] [P.IsIrreducible]
  {b : P.Base} [Fintype ι] [DecidableEq ι]

@[expose] public def HasRootWeight (k : ι)
    (X : Matrix (b.support ⊕ ι) (b.support ⊕ ι) R) : Prop :=
  ∀ l : b.support,
    ⁅RootPairing.GeckConstruction.h l, X⁆ = P.pairing k l • X

private lemma map_eMatrix_hasRootWeight (i : b.support) :
    HasRootWeight (P := P) (R := R) (b := b) i
      ((eMatrix i).map (algebraMap ℤ R)) := by
  intro l
  rw [map_eMatrix, RootPairing.GeckConstruction.lie_h_e]
  simp only [← Int.cast_smul_eq_zsmul R]
  congr 1
  exact RootPairing.Base.algebraMap_cartanMatrixIn_apply (S := ℤ) b i l

private lemma pairing_reflectionPerm_left (i : b.support) (k : ι)
    (l : b.support) :
    P.pairing (P.reflectionPerm i k) l =
      P.pairing k l - P.pairing i l * P.pairing k i := by
  change P.toLinearMap (P.root (P.reflectionPerm i k)) (P.coroot l) = _
  rw [P.root_reflectionPerm, P.reflection_apply_root]
  simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply]
  rw [P.root_coroot_eq_pairing, P.root_coroot_eq_pairing]
  ring

private lemma map_titsLift_conj_hasRootWeight (i : b.support) (k : ι)
    {X : Matrix (b.support ⊕ ι) (b.support ⊕ ι) R}
    (hX : HasRootWeight (P := P) (b := b) k X) :
    HasRootWeight (P := P) (b := b) (P.reflectionPerm i k)
      ((titsLift i).map (algebraMap ℤ R) * X *
        (titsLiftInv i).map (algebraMap ℤ R)) := by
  intro l
  let C := (titsLift i).map (algebraMap ℤ R)
  let D := (titsLiftInv i).map (algebraMap ℤ R)
  let h : b.support → Matrix (b.support ⊕ ι) (b.support ⊕ ι) R :=
    fun m => RootPairing.GeckConstruction.h (P := P) m
  let a : R := b.cartanMatrix i l
  have hCartan := map_titsLiftInv_conj_h (P := P) (R := R) (b := b) i l
  have hBracket := map_titsLift_conj_lie (P := P) (R := R) (b := b) i
    (h l - a • h i) X
  have ha : a = P.pairing i l :=
    RootPairing.Base.algebraMap_cartanMatrixIn_apply (S := ℤ) b i l
  change ⁅h l, C * X * D⁆ = P.pairing (P.reflectionPerm i k) l • (C * X * D)
  rw [show h l = C * (h l - a • h i) * D by
    have hCD := map_titsLift_mul_inv (P := P) (R := R) (b := b) i
    calc
      h l = (C * D) * h l * (C * D) := by rw [hCD, Matrix.one_mul, Matrix.mul_one]
      _ = C * (D * h l * C) * D := by noncomm_ring
      _ = C * (h l - a • h i) * D := by rw [hCartan]]
  rw [← hBracket]
  have hinner : ⁅h l - a • h i, X⁆ =
      (P.pairing k l - a * P.pairing k i) • X := by
    have hl := hX l
    have hi := hX i
    simp only [Ring.lie_def] at hl hi ⊢
    calc
      (h l - a • h i) * X - X * (h l - a • h i) =
          (h l * X - X * h l) - a • (h i * X - X * h i) := by
        rw [sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul]
        module
      _ = P.pairing k l • X - a • (P.pairing k i • X) := by rw [hl, hi]
      _ = (P.pairing k l - a * P.pairing k i) • X := by
        rw [smul_smul, sub_smul]
  rw [hinner, Matrix.mul_smul, Matrix.smul_mul]
  rw [pairing_reflectionPerm_left, ← ha]

public lemma map_titsConjugate_hasRootWeight (word : List b.support)
    (i : b.support) :
    HasRootWeight (P := P) (R := R) (b := b) (reflectionWord word i)
      ((titsConjugate word (eMatrix i)).map (algebraMap ℤ R)) := by
  induction word with
  | nil =>
      simpa [reflectionWord, titsConjugate_apply, titsWord, titsWordInv_nil]
        using map_eMatrix_hasRootWeight (P := P) (R := R) (b := b) i
  | cons j word ih =>
      have h := map_titsLift_conj_hasRootWeight (P := P) (R := R) (b := b) j
        (reflectionWord word i) ih
      simpa only [reflectionWord, titsConjugate_apply, titsWord,
        titsWordInv_cons, Matrix.map_mul, mul_assoc] using h


end
end RootPairing.IntegralGeckConstruction
