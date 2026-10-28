module

public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear.FieldAction
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear.OuterFixed.FieldDegree
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear.OuterFixed.Cocycle

/-!
# Fixed groups of outer semilinear involutions of binary PSL₂

Suppose an involution is explicitly given as entrywise application of a field
automorphism `σ` followed by conjugation by `g`. Trace invariance and the
trivial center of SL₂ in characteristic two show that `σ` is involutory and
that `g` satisfies the cocycle identity. Outerness makes `σ` nontrivial.
The determinant-one Hilbert–90 calculation then conjugates the automorphism
to `fieldAut σ`.

The actual fixed-subgroup equivalence identifies every fixed matrix with a
matrix over the fixed field. The fixed-field degree theorem gives `n = 2 * m`
and an isomorphism of that field with GF(2^m), completing the group descent.
The conclusion allows `m = 1`: an outer involution of PSL₂(4) has fixed group
PSL₂(2), with no simplicity assertion for this fixed group.

Source: GLS, Volume 4, Chapter 4, Lemma 3.4(c), linear case. This module proves
the descent from the explicit semilinear formula; arbitrary-automorphism
coverage is proved separately.
-/

namespace BenderSuzuki.ZD.Linear
open Matrix BenderSuzuki.MatrixGroups PFAppendixIII
variable {K L : Type*} [Field K] [Field L]
private def sl2RingEquiv (e : K ≃+* L) :
    SpecialLinearGroup (Fin 2) K ≃* SpecialLinearGroup (Fin 2) L where
  toFun := SpecialLinearGroup.map e.toRingHom
  invFun := SpecialLinearGroup.map e.symm.toRingHom
  left_inv A := by ext i j; exact e.symm_apply_apply (A i j)
  right_inv A := by ext i j; exact e.apply_symm_apply (A i j)
  map_mul' := (SpecialLinearGroup.map e.toRingHom).map_mul

variable [CharP K 2] [CharP L 2]
private noncomputable def psl2RingEquiv (e : K ≃+* L) :
    PSL2MatrixGroup K ≃* PSL2MatrixGroup L :=
  (sl2QuotientEquiv K).symm.trans ((sl2RingEquiv e).trans (sl2QuotientEquiv L))

/-- A coboundary conjugates the pure field action to the given semilinear action. -/
public theorem semilinear_congr_of_coboundary (σ : K ≃+* K) (g c : PSL2MatrixGroup K)
    (h : g = c * (fieldAut σ c)⁻¹) :
    MulAut.congr (MulAut.conj c) (fieldAut σ) = MulAut.conj g * fieldAut σ := by
  rw [h]
  ext x
  simp [MulAut.congr, MulAut.conj_apply, MulAut.conj_symm_apply, mul_assoc]

/-- Transport the entire fixed subgroup along the coboundary conjugation. -/
public noncomputable def semilinear_fixedEquiv_of_coboundary
    (σ : K ≃+* K) (g c : PSL2MatrixGroup K) (h : g = c * (fieldAut σ c)⁻¹) :
    (MulAut.conj g * fieldAut σ).fixedSubgroup ≃*
      PSL2MatrixGroup (FixedBy.subfield K σ) :=
  ((MulEquiv.subgroupCongr (congrArg MulAut.fixedSubgroup
    (semilinear_congr_of_coboundary σ g c h).symm)).trans
      (MulAut.fixedSubgroupCongr (MulAut.conj c) (fieldAut σ)).symm).trans
    (fieldAutFixedEquiv σ)

/-- The determinant-one cocycle calculation descends through SL₂ → PSL₂. -/
public theorem semilinear_coboundary [Finite K] (σ : K ≃+* K)
    (hs : Function.Involutive σ) (hne : σ ≠ RingEquiv.refl K)
    (g : PSL2MatrixGroup K) (hg : g * fieldAut σ g = 1) :
    ∃ c : PSL2MatrixGroup K, g = c * (fieldAut σ c)⁻¹ := by
  let e := sl2QuotientEquiv K
  let A := e.symm g
  have heq (X : SpecialLinearGroup (Fin 2) K) : e (sl2FieldAut σ X) = fieldAut σ (e X) :=
    (fieldAut_apply_pi σ X).symm
  have hA : A * sl2FieldAut σ A = 1 := by
    apply e.injective
    rw [map_mul, map_one]
    rw [heq]
    simpa [A, e] using hg
  obtain ⟨C, hC⟩ := involutory_sl2_cocycle_trivial σ hs hne A hA
  refine ⟨e C, ?_⟩
  have he := congrArg e hC
  rw [map_mul, map_inv] at he
  rw [heq] at he
  simpa only [A, MulEquiv.apply_symm_apply] using he

/-- Fixed-group descent for an explicitly semilinear outer involution of binary PSL₂. -/
public theorem outer_fixed_model_of_semilinear {n : ℕ} (hn : 2 ≤ n)
    (a : MulAut (PSL2BinaryMatrixGroup n)) (ha : a ^ 2 = 1)
    (g : PSL2BinaryMatrixGroup n)
    (σ : BinaryGaloisField n ≃+* BinaryGaloisField n)
    (heq : a = MulAut.conj g * fieldAut σ)
    (houter : ¬ ∃ b : PSL2BinaryMatrixGroup n, a = MulAut.conj b) :
    ∃ m : ℕ, 0 < m ∧ n = 2 * m ∧
      Nonempty (a.fixedSubgroup ≃* PSL2BinaryMatrixGroup m) := by
  have hsq : (MulAut.conj g * fieldAut σ) ^ 2 = 1 := by rw [← heq]; exact ha
  obtain ⟨hs, hg⟩ := semilinear_involution_data σ g hsq
  have hne : σ ≠ RingEquiv.refl _ := by
    intro h
    apply houter
    exact ⟨g, by rw [heq, h, fieldAut_refl, mul_one]⟩
  obtain ⟨c, hc⟩ := semilinear_coboundary σ hs hne g hg
  obtain ⟨m, hm, hnm, ⟨e⟩⟩ := binary_fixedField_model (by omega : 0 < n) σ hs hne
  refine ⟨m, hm, hnm, ⟨?_⟩⟩
  exact (MulEquiv.subgroupCongr (congrArg MulAut.fixedSubgroup heq)).trans
    ((semilinear_fixedEquiv_of_coboundary σ g c hc).trans (psl2RingEquiv e))

/-- The smallest case has fixed group PSL₂(2). -/
public theorem outer_fixed_model_degree_two
    (a : MulAut (PSL2BinaryMatrixGroup 2)) (ha : a ^ 2 = 1)
    (g : PSL2BinaryMatrixGroup 2)
    (σ : BinaryGaloisField 2 ≃+* BinaryGaloisField 2)
    (heq : a = MulAut.conj g * fieldAut σ)
    (houter : ¬ ∃ b : PSL2BinaryMatrixGroup 2, a = MulAut.conj b) :
    Nonempty (a.fixedSubgroup ≃* PSL2BinaryMatrixGroup 1) := by
  obtain ⟨m, hm, hnm, e⟩ := outer_fixed_model_of_semilinear (by decide) a ha g σ heq houter
  have : m = 1 := by omega
  subst m
  exact e
end BenderSuzuki.ZD.Linear
