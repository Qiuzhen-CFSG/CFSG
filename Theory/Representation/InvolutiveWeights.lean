module

public import Theory.Representation.AbelianAllWeights
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Character spaces for groups of exponent two

Over any field in which two is nonzero, the operators of an exponent-two
representation are diagonalizable: the projections are `(1 + T)/2` and
`(1 - T)/2`. For commuting operators the simultaneous eigenspaces therefore
span over the original field. A nonzero simultaneous eigenvalue function is
a multiplicative character. No algebraic closure or descent is needed.

This provides the field-of-definition step for the Sylow-eight eigenbasis in
Gorenstein, *Finite Groups*, §16.6, pp.482–483. The results also record that
faithfulness makes the occurring characters separate elements, and that a
decomposition with as many weights as dimensions consists of lines.
-/

open Polynomial
open scoped IsMulCommutative

namespace Representation

variable {E K V : Type*} [Field E] [Group K] [AddCommGroup V] [Module E V]

private theorem involutive_eigenspaces_span (T : Module.End E V)
    (hT : T ^ 2 = 1) (h2 : (2 : E) ≠ 0) :
    (⨆ a : E, T.eigenspace a) = ⊤ := by
  apply top_unique
  intro v _
  have hTv : T (T v) = v := by
    simpa [pow_two, Module.End.mul_apply] using LinearMap.congr_fun hT v
  have hp : (2 : E)⁻¹ • (v + T v) ∈ T.eigenspace 1 := by
    rw [Module.End.mem_eigenspace_iff]
    simp only [map_smul, map_add, hTv, one_smul]
    rw [add_comm]
  have hn : (2 : E)⁻¹ • (v - T v) ∈ T.eigenspace (-1) := by
    rw [Module.End.mem_eigenspace_iff]
    simp only [map_smul, map_sub, hTv, neg_one_smul]
    rw [← smul_neg, neg_sub]
  have hv : v = (2 : E)⁻¹ • (v + T v) + (2 : E)⁻¹ • (v - T v) := by
    rw [← smul_add, add_add_sub_cancel, ← two_smul E v, smul_smul,
      inv_mul_cancel₀ h2, one_smul]
  rw [hv]
  exact Submodule.add_mem _
    ((show T.eigenspace 1 ≤ ⨆ a : E, T.eigenspace a from le_iSup _ 1) hp)
    ((show T.eigenspace (-1) ≤ ⨆ a : E, T.eigenspace a from le_iSup _ (-1)) hn)

private theorem involutive_semisimple (σ : Representation E K V)
    (hpow : ∀ k : K, k ^ 2 = 1) (h2 : (2 : E) ≠ 0) (k : K) :
    Module.End.IsSemisimple (σ k) := by
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (p := (Polynomial.X : E[X]) ^ 2 - 1)
  · exact (Polynomial.X_pow_sub_one_separable_iff.mpr (by simpa using h2)).squarefree
  · have hp : σ k ^ 2 = 1 := by rw [← map_pow, hpow, map_one]
    simp [hp]

private theorem character_of_nonzero_joint_eigenspace (σ : Representation E K V)
    (w : K → E) (hw : (⨅ k, Module.End.eigenspace (σ k) (w k)) ≠ ⊥) :
    ∃ χ : K →* Eˣ, ∀ k, (χ k : E) = w k := by
  obtain ⟨v, hv, hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hw
  have he : ∀ k, σ k v = w k • v := by
    simpa only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff] using hv
  have h1 : w 1 = 1 := by
    apply smul_left_injective E hn
    simpa using (he 1).symm
  have hm : ∀ a b, w (a * b) = w a * w b := by
    intro a b
    apply smul_left_injective E hn
    change w (a * b) • v = (w a * w b) • v
    rw [← he, map_mul, Module.End.mul_apply, he b, map_smul, he a, smul_smul, mul_comm]
  have hne : ∀ k, w k ≠ 0 := by
    intro k hz
    have heq := hm k k⁻¹
    rw [mul_inv_cancel, h1, hz, zero_mul] at heq
    exact one_ne_zero heq
  exact ⟨{ toFun := fun k => Units.mk0 (w k) (hne k)
           map_one' := Units.ext h1
           map_mul' := fun a b => Units.ext (hm a b) }, fun _ => rfl⟩

variable [IsMulCommutative K] [FiniteDimensional E V]

/-- Simultaneous character spaces span an exponent-two representation over
the original field, provided its characteristic is not two. -/
public theorem iSup_characterWeightSpace_eq_top_of_involutive (σ : Representation E K V)
    (hpow : ∀ k : K, k ^ 2 = 1) (h2 : (2 : E) ≠ 0) :
    (⨆ χ : σ.CharacterWeight, σ.characterWeightSpace χ.val) = ⊤ := by
  have hc : ∀ a b, Commute (σ a) (σ b) := by
    intro a b
    change σ a * σ b = σ b * σ a
    simp [← map_mul, mul_comm]
  have heq : ∀ k a, Module.End.maxGenEigenspace (σ k) a =
      Module.End.eigenspace (σ k) a := by
    intro k a
    exact (involutive_semisimple σ hpow h2 k).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace a
  have ht : (⨆ w : K → E, ⨅ k, Module.End.eigenspace (σ k) (w k)) = ⊤ := by
    have hs : ∀ k, ⨆ a, Module.End.maxGenEigenspace (σ k) a = ⊤ := by
      intro k
      simpa only [heq] using involutive_eigenspaces_span (σ k)
        (by rw [← map_pow, hpow, map_one]) h2
    simpa only [heq] using
      Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
        σ (fun a b _ => hc a b) hs
  apply top_unique
  rw [← ht]
  refine iSup_le fun w => ?_
  by_cases hw : (⨅ k, Module.End.eigenspace (σ k) (w k)) = ⊥
  · simp [hw]
  obtain ⟨χ, hχ⟩ := character_of_nonzero_joint_eigenspace σ w hw
  have hn : σ.characterWeightSpace χ ≠ ⊥ := by
    simpa only [characterWeightSpace, hχ] using hw
  simpa only [characterWeightSpace, hχ] using
    (le_iSup (fun χ : σ.CharacterWeight => σ.characterWeightSpace χ.val) ⟨χ, hn⟩)

/-- The occurring characters of a faithful exponent-two representation
separate elements over the coefficient field itself. -/
public theorem eq_of_characterWeight_values_of_involutive (σ : Representation E K V)
    (hσ : Function.Injective σ) (hpow : ∀ k : K, k ^ 2 = 1) (h2 : (2 : E) ≠ 0)
    (a b : K) (hab : ∀ χ : σ.CharacterWeight, χ.val a = χ.val b) : a = b := by
  apply hσ
  apply LinearMap.eqLocus_eq_top.mp
  apply top_unique
  rw [← σ.iSup_characterWeightSpace_eq_top_of_involutive hpow h2]
  refine iSup_le fun χ v hv => ?_
  simp only [characterWeightSpace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff] at hv
  change σ a v = σ b v
  rw [hv a, hv b, hab χ]

/-- Faithfulness on a nontrivial exponent-two group supplies a nontrivial
occurring character without extending scalars. -/
public theorem exists_nontrivial_characterWeight_of_involutive [Nontrivial K]
    (σ : Representation E K V) (hσ : Function.Injective σ)
    (hpow : ∀ k : K, k ^ 2 = 1) (h2 : (2 : E) ≠ 0) :
    ∃ χ : σ.CharacterWeight, χ.val ≠ 1 := by
  obtain ⟨k, hk⟩ := exists_ne (1 : K)
  by_contra! hn
  apply hk
  apply eq_of_characterWeight_values_of_involutive σ hσ hpow h2
  intro χ
  simp [hn χ]

/-- Saturating the dimension bound makes every occurring character space a
line, also over a field that is not algebraically closed. -/
public theorem characterWeight_finrank_one_of_involutive_card_eq
    (σ : Representation E K V) (hpow : ∀ k : K, k ^ 2 = 1) (h2 : (2 : E) ≠ 0)
    (horder : (Nat.card K : E) ≠ 0)
    (hcard : Nat.card σ.CharacterWeight = Module.finrank E V) (χ : σ.CharacterWeight) :
    Module.finrank E (σ.characterWeightSpace χ.val) = 1 := by
  classical
  let := (σ.characterWeight_card_le horder).1
  let := Fintype.ofFinite σ.CharacterWeight
  let W : σ.CharacterWeight → Submodule E V := fun χ => σ.characterWeightSpace χ.val
  have hind : iSupIndep W :=
    (σ.characterWeightSpace_independent horder).comp Subtype.val_injective
  have hi : DirectSum.IsInternal W :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind
      (σ.iSup_characterWeightSpace_eq_top_of_involutive hpow h2)
  have hsum : ∑ i, Module.finrank E (W i) = Module.finrank E V := by
    rw [← Module.finrank_directSum]
    exact (LinearEquiv.ofBijective (DirectSum.coeLinearMap W) hi).finrank_eq
  have hone (i : σ.CharacterWeight) : 1 ≤ Module.finrank E (W i) :=
    Submodule.one_le_finrank_iff.mpr i.property
  have heq : (∑ _i : σ.CharacterWeight, 1) = ∑ i, Module.finrank E (W i) := by
    simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
      ← Nat.card_eq_fintype_card, hsum] using hcard
  exact ((Finset.sum_eq_sum_iff_of_le (fun i _ => hone i)).mp heq χ
    (Finset.mem_univ χ)).symm

end Representation
