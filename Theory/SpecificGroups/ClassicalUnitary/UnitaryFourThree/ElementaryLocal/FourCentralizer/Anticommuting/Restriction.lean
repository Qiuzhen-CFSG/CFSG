module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.Model
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ElementaryLocal.FourCentralizer.Lifts
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ElementaryLocal.FourCentralizer.Anticommuting.UnitaryPlane
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.StandardInvolution
public import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Faithful unitary restriction for an anticommuting pair

Suppose a unitary change of basis identifies a scalar multiple of the first
lift with diag(-1,-1,1,1). After that change of basis, its common centralizer
with an anticommuting second lift is block diagonal. The second lift exchanges
the two coordinate planes, and its invertible upper-right block determines the
second centralizer block from the first. Thus restriction to the first plane
is faithful. The restricted block preserves the identity Hermitian form, so
its image lies in the actual full unitary plane group over Nine.

This is a conditional local linear-algebra ingredient, with the conjugator
supplied explicitly. Conjugator existence and the centralizer-order deduction
belong to the parent module. The unitary convention is exact isometry over
GF(9), as in `refs/KGroup/GLS3/chapter2.tex`, §2.6; the local application is
Aschbacher–Smith, Theorem 0.1.2(4), printed p.4 (also Theorem 0.1.1(4),
printed p.482), in `refs/quasithin.pdf`.
-/

open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal

noncomputable section

namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ElementaryLocal.FourCentralizer.Anticommuting
private abbrev F := FiniteField.Nine
private abbrev M2 := Matrix (Fin 2) (Fin 2) F
private abbrev MB := Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F
private abbrev splitMatrix : Matrix (Fin 4) (Fin 4) F ≃+* MB :=
  Matrix.reindexRingEquiv F (finSumFinEquiv (m := 2) (n := 2)).symm
private theorem split_adj (A : Matrix (Fin 4) (Fin 4) F) :
    splitMatrix A.conjTranspose = (splitMatrix A).conjTranspose := rfl
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
private theorem upper_unitary (M : MB) (hM : M = fromBlocks M.toBlocks₁₁ 0 0 M.toBlocks₂₂)
    (hU : M.conjTranspose * M = 1) :
    M.toBlocks₁₁.conjTranspose * M.toBlocks₁₁ = 1 := by
  rw [hM] at hU
  have h := congrArg Matrix.toBlocks₁₁ hU
  simpa [fromBlocks_conjTranspose, fromBlocks_multiply, ← fromBlocks_one] using h
private def upperUnit (M : MB)
    (h : M.toBlocks₁₁.conjTranspose * M.toBlocks₁₁ = 1) : GL (Fin 2) F where
  val := M.toBlocks₁₁
  inv := M.toBlocks₁₁.conjTranspose
  val_inv := mul_eq_one_comm.mpr h
  inv_val := h
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


private abbrev U4 := (form 4).unitarySubgroup
private abbrev splitGL : GL (Fin 4) F →* GL (Fin 2 ⊕ Fin 2) F :=
  Units.map splitMatrix.toMonoidHom
private def conjugateUnitary (C : U4) : SU →* U4 :=
  (MulAut.conj C⁻¹).toMonoidHom.comp
    (Subgroup.inclusion (form 4).specialSubgroup_le_unitarySubgroup)
private def rho (C : U4) : SU →* GL (Fin 2 ⊕ Fin 2) F :=
  splitGL.comp ((form 4).unitarySubgroup.subtype.comp (conjugateUnitary C))
private theorem rho_val (C : U4) (x : SU) :
    (rho C x).val = splitMatrix (MulAut.conj C.val⁻¹ x.val).val := rfl
private theorem rho_injective (C : U4) : Function.Injective (rho C) := by
  intro x y h
  apply Subtype.ext
  apply (MulAut.conj C.val⁻¹).injective
  apply Units.ext
  apply splitMatrix.injective
  exact congrArg Units.val h
/-- Unitary conjugation and coordinate reindexing retain the identity form. -/
private theorem rho_unitary (C : U4) (x : SU) :
    (rho C x).val.conjTranspose * (rho C x).val = 1 := by
  have h := ((form 4).mem_unitarySubgroup_iff _).mp (conjugateUnitary C x).property
  change (conjugateUnitary C x).val.val.conjTranspose * 1 *
    (conjugateUnitary C x).val.val = 1 at h
  rw [mul_one] at h
  have hh := congrArg splitMatrix h
  rw [map_mul, map_one, split_adj] at hh
  exact hh
private theorem conjugate_anticommute (A B P : GL (Fin 4) F)
    (h : A.val * B.val = -(B.val * A.val)) :
    (MulAut.conj P A).val * (MulAut.conj P B).val =
      -((MulAut.conj P B).val * (MulAut.conj P A).val) := by
  change (P.val * A.val * P.inv) * (P.val * B.val * P.inv) =
    -((P.val * B.val * P.inv) * (P.val * A.val * P.inv))
  have hc (X : Matrix (Fin 4) (Fin 4) F) : P.inv * (P.val * X) = X := by
    rw [← mul_assoc, P.inv_val, one_mul]
  simp only [mul_assoc, hc]
  rw [← mul_assoc A.val B.val, h, neg_mul, mul_neg, mul_assoc]
private theorem standard_of_conjugator (a : SU) (u : Fˣ) (C : U4)
    (hC : C.val * standardInvolutionGL * C.val⁻¹ = GeneralLinearGroup.scalar (Fin 4) u * a.val) :
    MulAut.conj C.val⁻¹ (GeneralLinearGroup.scalar (Fin 4) u * a.val) =
      standardInvolutionGL := by
  rw [← hC]
  simp [mul_assoc]
private theorem rho_offDiagonal (a b : SU) (u : Fˣ) (C : U4)
    (hab : a.val.val * b.val.val = -(b.val.val * a.val.val))
    (hC : C.val * standardInvolutionGL * C.val⁻¹ = GeneralLinearGroup.scalar (Fin 4) u * a.val) :
    (rho C b).val = fromBlocks 0 (rho C b).val.toBlocks₁₂ (rho C b).val.toBlocks₂₁ 0 := by
  have hs := congrArg Units.val (GeneralLinearGroup.scalar_commute u b.val)
  simp only [Units.val_mul] at hs
  have hab' : (GeneralLinearGroup.scalar (Fin 4) u * a.val).val * b.val.val =
      -(b.val.val * (GeneralLinearGroup.scalar (Fin 4) u * a.val).val) := by
    simp only [Units.val_mul]
    rw [mul_assoc, hab, mul_neg, ← mul_assoc, hs, mul_assoc]
  have h := conjugate_anticommute _ _ C.val⁻¹ hab'
  rw [standard_of_conjugator a u C hC] at h
  have hh := congrArg splitMatrix h
  simp only [map_mul, map_neg] at hh
  change splitMatrix standardInvolutionMatrix * (rho C b).val =
    -((rho C b).val * splitMatrix standardInvolutionMatrix) at hh
  rw [split_standard] at hh
  exact offDiagonal_of_anticommutes _ hh
private theorem rho_diagonal (a b : SU) (u : Fˣ) (C : U4)
    (hC : C.val * standardInvolutionGL * C.val⁻¹ = GeneralLinearGroup.scalar (Fin 4) u * a.val)
    (x : Subgroup.centralizer ({a,b} : Set SU)) :
    (rho C x.val).val = fromBlocks (rho C x.val).val.toBlocks₁₁ 0 0
      (rho C x.val).val.toBlocks₂₂ := by
  have hx : Commute x.val a :=
    (Subgroup.mem_centralizer_iff.mp x.property a (by simp)).symm
  have hx' : Commute x.val.val (GeneralLinearGroup.scalar (Fin 4) u * a.val) :=
    (show Commute x.val.val (GeneralLinearGroup.scalar (Fin 4) u) from
      (GeneralLinearGroup.scalar_commute u x.val.val).symm).mul_right (hx.map SU.subtype)
  have h := (hx'.map (MulAut.conj C.val⁻¹)).eq
  rw [standard_of_conjugator a u C hC] at h
  have hh := congrArg (fun g : GL (Fin 4) F => splitMatrix g.val) h
  simp only [Units.val_mul, map_mul] at hh
  change (rho C x.val).val * splitMatrix standardInvolutionMatrix =
    splitMatrix standardInvolutionMatrix * (rho C x.val).val at hh
  rw [split_standard] at hh
  exact diagonal_of_commutes _ hh
/-- The first diagonal block is an invertible isometry, with its adjoint as inverse. -/
private def restriction (a b : SU) (u : Fˣ) (C : U4)
    (hC : C.val * standardInvolutionGL * C.val⁻¹ = GeneralLinearGroup.scalar (Fin 4) u * a.val) :
    Subgroup.centralizer ({a,b} : Set SU) →* FullUnitaryTwo where
  toFun x := ⟨upperUnit (rho C x.val).val
      (upper_unitary _ (rho_diagonal a b u C hC x) (rho_unitary C x.val)), by
    rw [(form 2).mem_unitarySubgroup_iff]
    change (rho C x.val).val.toBlocks₁₁.conjTranspose * 1 *
      (rho C x.val).val.toBlocks₁₁ = 1
    rw [mul_one]
    exact upper_unitary _ (rho_diagonal a b u C hC x) (rho_unitary C x.val)⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    change (rho C 1).val.toBlocks₁₁ = 1
    rw [map_one]
    change (1 : MB).toBlocks₁₁ = 1
    rw [← fromBlocks_one]
    rfl
  map_mul' x y := by
    apply Subtype.ext
    apply Units.ext
    change (rho C (x.val * y.val)).val.toBlocks₁₁ =
      (rho C x.val).val.toBlocks₁₁ * (rho C y.val).val.toBlocks₁₁
    rw [map_mul]
    change ((rho C x.val).val * (rho C y.val).val).toBlocks₁₁ = _
    conv_lhs => rw [rho_diagonal a b u C hC x, rho_diagonal a b u C hC y]
    simp only [fromBlocks_multiply, toBlocks_fromBlocks₁₁, mul_zero, add_zero]
/-- Conjugating the common centralizer into the standard two-plane decomposition
and restricting to the first plane gives a faithful homomorphism into the actual
identity-form unitary plane group. The supplied conjugator is the only geometric
input; neither lift needs a projective-square hypothesis here. -/
public theorem exists_unitary_plane_embedding_of_conjugator
    (a b : SU) (u : FiniteField.Nineˣ) (C : (form 4).unitarySubgroup)
    (hab : a.val.val * b.val.val = -(b.val.val * a.val.val))
    (hC : C.val * standardInvolutionGL * C.val⁻¹ = GeneralLinearGroup.scalar (Fin 4) u * a.val) :
    ∃ f : Subgroup.centralizer ({a,b} : Set SU) →* FullUnitaryTwo, Function.Injective f := by
  refine ⟨restriction a b u C hC, ?_⟩
  intro x y h
  apply Subtype.ext
  apply rho_injective C
  apply Units.ext
  have hb (z : Subgroup.centralizer ({a,b} : Set SU)) :
      (rho C z.val).val * (rho C b).val = (rho C b).val * (rho C z.val).val := by
    have hz : Commute z.val b :=
      (Subgroup.mem_centralizer_iff.mp z.property b (by simp)).symm
    exact congrArg Units.val (hz.map (rho C)).eq
  exact upper_injective (rho C b) (rho_offDiagonal a b u C hab hC)
    _ _ (rho_diagonal a b u C hC x) (rho_diagonal a b u C hC y)
    (hb x) (hb y) (congrArg (fun z : FullUnitaryTwo => z.val.val) h)

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ElementaryLocal.FourCentralizer.Anticommuting
