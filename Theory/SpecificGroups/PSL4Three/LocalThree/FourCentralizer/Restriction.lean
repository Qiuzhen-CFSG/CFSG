module

public import Theory.SpecificGroups.PSL4Three.LocalThree.FourCentralizer.Eigenbasis
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Faithful plane restriction for anticommuting matrices over F₃

After a change of basis, the first matrix is diag(-1,-1,1,1). The common
centralizer is block diagonal and the second matrix is block antidiagonal.
Its invertible upper-right block determines the second centralizer block
from the first, giving an embedding into GL₂(3), of order 48.

The block argument adapts the existing unitary plane restriction proof,
using ordinary invertibility for the restricted block. No form is imposed.
Source application: Aschbacher–Smith, Theorem 0.1.2(4), printed p.4,
repeated as Theorem 0.1.1(4), printed p.482 of `refs/quasithin.pdf`.
-/

open Matrix
open Matrix.PSL4Three.TwoLocal
noncomputable section
namespace Matrix.PSL4Three.LocalThree.FourCentralizer.Anticommuting

private abbrev F := ZMod 3
private abbrev M2 := Matrix (Fin 2) (Fin 2) F
private abbrev MB := Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F
private abbrev splitMatrix : Matrix (Fin 4) (Fin 4) F ≃+* MB :=
  Matrix.reindexRingEquiv F (finSumFinEquiv (m := 2) (n := 2)).symm
private theorem split_standard : splitMatrix standardInvolutionMatrix =
    fromBlocks (-1 : M2) 0 0 (1 : M2) := by decide
private theorem eq_zero_of_eq_neg (A : M2) (h : A = -A) : A = 0 := by
  funext i j
  exact (by decide : ∀ x : F, x = -x → x = 0) (A i j)
    (congrArg (fun M : M2 => M i j) h)
/-- Commutation with the two distinct scalar eigenvalues forces block diagonality. -/
private theorem diagonal_of_commutes (M : MB)
    (h : M * fromBlocks (-1 : M2) 0 0 (1 : M2) =
      fromBlocks (-1 : M2) 0 0 (1 : M2) * M) :
    M = fromBlocks M.toBlocks₁₁ 0 0 M.toBlocks₂₂ := by
  rw [← fromBlocks_toBlocks M] at h
  simp only [fromBlocks_multiply, mul_neg, mul_one, mul_zero, zero_mul,
    zero_add, add_zero, neg_mul, one_mul, fromBlocks_inj] at h
  have h12 := eq_zero_of_eq_neg _ h.2.1
  have h21 := eq_zero_of_eq_neg _ h.2.2.1.symm
  simpa only [h12, h21] using (fromBlocks_toBlocks M).symm
/-- Anticommutation exchanges the two coordinate planes. -/
private theorem offDiagonal_of_anticommutes (M : MB)
    (h : fromBlocks (-1 : M2) 0 0 (1 : M2) * M =
      -(M * fromBlocks (-1 : M2) 0 0 (1 : M2))) :
    M = fromBlocks 0 M.toBlocks₁₂ M.toBlocks₂₁ 0 := by
  rw [← fromBlocks_toBlocks M] at h
  simp only [fromBlocks_multiply, mul_neg, mul_one, mul_zero, zero_mul,
    zero_add, add_zero, neg_mul, one_mul, fromBlocks_neg, neg_neg, fromBlocks_inj] at h
  have h11 := eq_zero_of_eq_neg _ h.1.symm
  have h22 := eq_zero_of_eq_neg _ h.2.2.2
  simpa only [h11, h22] using (fromBlocks_toBlocks M).symm
/-- The inverse of the full matrix supplies an inverse for its upper-right block. -/
private def offUnit (B : GL (Fin 2 ⊕ Fin 2) F)
    (hB : B.val = fromBlocks 0 B.val.toBlocks₁₂ B.val.toBlocks₂₁ 0) : GL (Fin 2) F where
  val := B.val.toBlocks₁₂
  inv := B.inv.toBlocks₂₁
  val_inv := by
    have h := B.val_inv
    rw [hB, ← fromBlocks_toBlocks B.inv] at h
    have hh := congrArg Matrix.toBlocks₁₁ h
    simpa [fromBlocks_multiply, ← fromBlocks_one] using hh
  inv_val := by
    have h := B.inv_val
    rw [hB, ← fromBlocks_toBlocks B.inv] at h
    have hh := congrArg Matrix.toBlocks₂₂ h
    simpa [fromBlocks_multiply, ← fromBlocks_one] using hh
/-- Commutation with the invertible upper-right block determines the second
diagonal block from the first. -/
private theorem upper_injective (B : GL (Fin 2 ⊕ Fin 2) F)
    (hB : B.val = fromBlocks 0 B.val.toBlocks₁₂ B.val.toBlocks₂₁ 0)
    (M N : MB)
    (hM : M = fromBlocks M.toBlocks₁₁ 0 0 M.toBlocks₂₂)
    (hN : N = fromBlocks N.toBlocks₁₁ 0 0 N.toBlocks₂₂)
    (hMB : M * B.val = B.val * M) (hNB : N * B.val = B.val * N)
    (h : M.toBlocks₁₁ = N.toBlocks₁₁) : M = N := by
  have hm := congrArg Matrix.toBlocks₁₂ hMB
  have hn := congrArg Matrix.toBlocks₁₂ hNB
  rw [hM, hB] at hm
  rw [hN, hB] at hn
  simp only [fromBlocks_multiply, toBlocks_fromBlocks₁₂, mul_zero, zero_mul,
    zero_add, add_zero] at hm hn
  have hd : M.toBlocks₂₂ = N.toBlocks₂₂ := by
    apply (offUnit B hB).mul_right_inj.mp
    change B.val.toBlocks₁₂ * M.toBlocks₂₂ = B.val.toBlocks₁₂ * N.toBlocks₂₂
    rw [← hm, ← hn, h]
  rw [hM, hN, h, hd]


private abbrev GL4 := GL (Fin 4) F
private abbrev CPair (a b : GL4) := Subgroup.centralizer ({a, b} : Set GL4)
private abbrev splitGL : GL4 →* GL (Fin 2 ⊕ Fin 2) F :=
  Units.map splitMatrix.toMonoidHom
private def rho (C : GL4) : GL4 →* GL (Fin 2 ⊕ Fin 2) F :=
  splitGL.comp (MulAut.conj C⁻¹).toMonoidHom
private theorem rho_injective (C : GL4) : Function.Injective (rho C) := by
  intro x y h
  apply (MulAut.conj C⁻¹).injective
  apply Units.ext
  apply splitMatrix.injective
  exact congrArg Units.val h
private theorem conjugate_anticommute (A B P : GL4)
    (h : A.val * B.val = -(B.val * A.val)) :
    (MulAut.conj P A).val * (MulAut.conj P B).val =
      -((MulAut.conj P B).val * (MulAut.conj P A).val) := by
  change (P.val * A.val * P.inv) * (P.val * B.val * P.inv) =
    -((P.val * B.val * P.inv) * (P.val * A.val * P.inv))
  have hc (X : Matrix (Fin 4) (Fin 4) F) : P.inv * (P.val * X) = X := by
    rw [← mul_assoc, P.inv_val, one_mul]
  simp only [mul_assoc, hc]
  rw [← mul_assoc A.val B.val, h, neg_mul, mul_neg, mul_assoc]
private theorem standard_of_conjugator (a C : GL4)
    (hC : C * splitInvolutionGL * C⁻¹ = a) :
    MulAut.conj C⁻¹ a = splitInvolutionGL := by
  rw [← hC]
  simp [mul_assoc]
private theorem rho_offDiagonal (a b C : GL4)
    (hab : a.val * b.val = -(b.val * a.val))
    (hC : C * splitInvolutionGL * C⁻¹ = a) :
    (rho C b).val = fromBlocks 0 (rho C b).val.toBlocks₁₂ (rho C b).val.toBlocks₂₁ 0 := by
  have h := conjugate_anticommute a b C⁻¹ hab
  rw [standard_of_conjugator a C hC] at h
  have hh := congrArg splitMatrix h
  simp only [map_mul, map_neg] at hh
  change splitMatrix standardInvolutionMatrix * (rho C b).val =
    -((rho C b).val * splitMatrix standardInvolutionMatrix) at hh
  rw [split_standard] at hh
  exact offDiagonal_of_anticommutes _ hh
private theorem rho_diagonal (a b C : GL4)
    (hC : C * splitInvolutionGL * C⁻¹ = a)
    (x : CPair a b) :
    (rho C x.val).val = fromBlocks (rho C x.val).val.toBlocks₁₁ 0 0
      (rho C x.val).val.toBlocks₂₂ := by
  have hx : Commute x.val a :=
    (Subgroup.mem_centralizer_iff.mp x.property a (by simp)).symm
  have h := (hx.map (MulAut.conj C⁻¹)).eq
  rw [standard_of_conjugator a C hC] at h
  have hh := congrArg (fun g : GL4 => splitMatrix g.val) h
  simp only [Units.val_mul, map_mul] at hh
  change (rho C x.val).val * splitMatrix standardInvolutionMatrix =
    splitMatrix standardInvolutionMatrix * (rho C x.val).val at hh
  rw [split_standard] at hh
  exact diagonal_of_commutes _ hh

private def upperUnit (M : GL (Fin 2 ⊕ Fin 2) F)
    (hM : M.val = fromBlocks M.val.toBlocks₁₁ 0 0 M.val.toBlocks₂₂) : GL (Fin 2) F where
  val := M.val.toBlocks₁₁
  inv := M.inv.toBlocks₁₁
  val_inv := by
    have h := M.val_inv
    rw [hM, ← fromBlocks_toBlocks M.inv] at h
    have hh := congrArg Matrix.toBlocks₁₁ h
    simpa [fromBlocks_multiply, ← fromBlocks_one] using hh
  inv_val := by
    have h := M.inv_val
    rw [hM, ← fromBlocks_toBlocks M.inv] at h
    have hh := congrArg Matrix.toBlocks₁₁ h
    simpa [fromBlocks_multiply, ← fromBlocks_one] using hh

private def restriction (a b C : GL4)
    (hC : C * splitInvolutionGL * C⁻¹ = a) : CPair a b →* GL (Fin 2) F where
  toFun x := upperUnit (rho C x.val) (rho_diagonal a b C hC x)
  map_one' := by
    apply Units.ext
    change (rho C 1).val.toBlocks₁₁ = 1
    rw [map_one]
    change (1 : MB).toBlocks₁₁ = 1
    rw [← fromBlocks_one]
    rfl
  map_mul' x y := by
    apply Units.ext
    change (rho C (x.val * y.val)).val.toBlocks₁₁ =
      (rho C x.val).val.toBlocks₁₁ * (rho C y.val).val.toBlocks₁₁
    rw [map_mul]
    change ((rho C x.val).val * (rho C y.val).val).toBlocks₁₁ = _
    conv_lhs => rw [rho_diagonal a b C hC x, rho_diagonal a b C hC y]
    simp only [fromBlocks_multiply, toBlocks_fromBlocks₁₁, mul_zero, add_zero]

/-- The first plane faithfully represents the common centralizer. -/
public theorem exists_plane_embedding_of_conjugator (a b C : GL (Fin 4) (ZMod 3))
    (hab : a.val * b.val = -(b.val * a.val))
    (hC : C * splitInvolutionGL * C⁻¹ = a) :
    ∃ f : Subgroup.centralizer ({a, b} : Set (GL (Fin 4) (ZMod 3))) →*
      GL (Fin 2) (ZMod 3), Function.Injective f := by
  refine ⟨restriction a b C hC, ?_⟩
  intro x y h
  apply Subtype.ext
  apply rho_injective C
  apply Units.ext
  have hb (z : CPair a b) :
      (rho C z.val).val * (rho C b).val = (rho C b).val * (rho C z.val).val := by
    have hz : Commute z.val b :=
      (Subgroup.mem_centralizer_iff.mp z.property b (by simp)).symm
    exact congrArg Units.val (hz.map (rho C)).eq
  exact upper_injective (rho C b) (rho_offDiagonal a b C hab hC)
    _ _ (rho_diagonal a b C hC x) (rho_diagonal a b C hC y)
    (hb x) (hb y) (congrArg Units.val h)

/-- The common centralizer of an involution and an invertible anticommuting
matrix embeds in GL₂(3), so its order has no factor nine. -/
public theorem centralizer_not_nine_dvd_of_square_one (a b : GL (Fin 4) (ZMod 3))
    (ha : a ^ 2 = 1) (ht : trace a.val = 0)
    (hab : a.val * b.val = -(b.val * a.val)) :
    ¬ 3 ^ 2 ∣ Nat.card (Subgroup.centralizer ({a, b} : Set (GL (Fin 4) (ZMod 3)))) := by
  obtain ⟨C, hC⟩ := exists_linear_conjugator_of_trace_zero a ha ht
  obtain ⟨f, hf⟩ := exists_plane_embedding_of_conjugator a b C hab hC
  have hc : Nat.card (GL (Fin 2) (ZMod 3)) = 48 := by
    rw [Matrix.card_GL_field]
    decide
  intro h
  have hh := h.trans (Subgroup.card_dvd_of_injective f hf)
  rw [hc] at hh
  norm_num at hh

end Matrix.PSL4Three.LocalThree.FourCentralizer.Anticommuting
