module

public import Theory.SpecificGroups.SL3.InvolutionBlock
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Basis.Fin

/-!
# Linear eigenbases for involutions in dimension three

In characteristic different from two, the half-difference and half-sum
projections split the space into the negative and positive eigenspaces.
The determinant is `(-1) ^ dim V₋`; determinant one and nontriviality therefore
force dimensions two and one. Joining bases of these spaces gives a conjugator
to `diag(-1,-1,1)`. The argument also applies in characteristic three.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma A.3.21(a), printed p. 55 (PDF p. 66).
-/

public section

open Matrix
open scoped Matrix
open Module
open Submodule

namespace Matrix.SL3

variable {F : Type*} [Field F]

private def involutionLin (M : Matrix (Fin 3) (Fin 3) F) : Module.End F (Fin 3 → F) :=
  Matrix.toLin' M

private def negSpace (M : Matrix (Fin 3) (Fin 3) F) : Submodule F (Fin 3 → F) :=
  (involutionLin M).eigenspace (-1)

private def posSpace (M : Matrix (Fin 3) (Fin 3) F) : Submodule F (Fin 3 → F) :=
  (involutionLin M).eigenspace 1

private theorem involution_isCompl (h2 : (2 : F) ≠ 0)
    (M : Matrix (Fin 3) (Fin 3) F) (hsq : M * M = 1) :
    IsCompl (negSpace M) (posSpace M) := by
  let f := involutionLin M
  have hf : f * f = 1 := by
    apply LinearMap.ext
    intro x
    change M *ᵥ (M *ᵥ x) = x
    calc
      M *ᵥ (M *ᵥ x) = (M * M) *ᵥ x := Matrix.mulVec_mulVec x M M
      _ = x := by rw [hsq]; simp
  have hfx (x : Fin 3 → F) : f (f x) = x := by
    simpa [Module.End.mul_apply] using congrArg (fun g : Module.End F (Fin 3 → F) => g x) hf
  have hsum : negSpace M ⊔ posSpace M = ⊤ := by
    apply top_unique
    intro x hx
    let u : Fin 3 → F := (2 : F)⁻¹ • (x - f x)
    let v : Fin 3 → F := (2 : F)⁻¹ • (x + f x)
    have hu : u ∈ negSpace M := by
      change u ∈ f.eigenspace (-1)
      rw [Module.End.mem_eigenspace_iff]
      dsimp [u, f]
      rw [map_smul, map_sub, hfx]
      simp [sub_eq_add_neg, add_comm]
    have hv : v ∈ posSpace M := by
      change v ∈ f.eigenspace 1
      rw [Module.End.mem_eigenspace_iff]
      dsimp [v, f]
      rw [map_smul, map_add, hfx]
      simp [add_comm]
    have huv : u + v = x := by
      dsimp [u, v]
      rw [← smul_add]
      ext i
      abel_nf
      simp [smul_eq_mul, h2]
    rw [← huv]
    exact add_mem_sup hu hv
  have hdis : Disjoint (negSpace M) (posSpace M) := by
    rw [disjoint_iff]
    apply le_antisymm
    · rintro x ⟨hxneg, hxpos⟩
      change x ∈ f.eigenspace (-1) at hxneg
      change x ∈ f.eigenspace 1 at hxpos
      rw [Module.End.mem_eigenspace_iff] at hxneg hxpos
      have he : (-1 : F) • x = (1 : F) • x := hxneg.symm.trans hxpos
      have he0 : -x = x := by simpa using he
      have he' : x + x = 0 := (eq_neg_iff_add_eq_zero.mp he0.symm)
      have he'' : (2 : F) • x = 0 := by simpa [two_smul] using he'
      have : x = 0 := by
        exact (smul_eq_zero.mp he'').resolve_left h2
      rw [show x = 0 from this]
      exact Submodule.zero_mem _
    · exact bot_le
  exact ⟨hdis, by rw [codisjoint_iff]; exact hsum⟩

private theorem det_involution (h2 : (2 : F) ≠ 0)
    (M : Matrix (Fin 3) (Fin 3) F) (hsq : M * M = 1) :
    M.det = (-1 : F) ^ finrank F (negSpace M) := by
  let e := (negSpace M).prodEquivOfIsCompl (posSpace M) (involution_isCompl h2 M hsq)
  let g : Module.End F (negSpace M × posSpace M) :=
    LinearMap.prodMap ((-1 : F) • (1 : Module.End F (negSpace M))) 1
  have he (x : negSpace M × posSpace M) : involutionLin M (e x) = e (g x) := by
    have hn := (Module.End.mem_eigenspace_iff.mp x.1.property)
    have hp := (Module.End.mem_eigenspace_iff.mp x.2.property)
    change involutionLin M ((x.1 : Fin 3 → F) + x.2) =
      (-1 : F) • (x.1 : Fin 3 → F) + x.2
    rw [map_add, hn, hp, one_smul]
  have hf : involutionLin M = e.toLinearMap ∘ₗ g ∘ₗ e.symm.toLinearMap := by
    apply LinearMap.ext
    intro x
    simpa using he (e.symm x)
  calc
    M.det = (involutionLin M).det := by rw [← LinearMap.det_toMatrix']; simp [involutionLin]
    _ = g.det := by rw [hf, LinearMap.det_conj]
    _ = (-1 : F) ^ finrank F (negSpace M) := by
      simp [g, LinearMap.det_prodMap, LinearMap.det_smul]

private theorem dimensions (h2 : (2 : F) ≠ 0)
    (M : Matrix (Fin 3) (Fin 3) F) (hsq : M * M = 1)
    (hne : M ≠ 1) (hdet : M.det = 1) :
    finrank F (negSpace M) = 2 ∧ finrank F (posSpace M) = 1 := by
  have hc := involution_isCompl h2 M hsq
  have hsum : finrank F (negSpace M) + finrank F (posSpace M) = 3 := by
    simpa using Submodule.finrank_add_eq_of_isCompl hc
  have hd : (-1 : F) ^ finrank F (negSpace M) = 1 :=
    (det_involution h2 M hsq).symm.trans hdet
  have hn : finrank F (negSpace M) ≠ 0 := by
    intro hz
    have hz' : negSpace M = ⊥ := Submodule.finrank_eq_zero.mp hz
    have hp : posSpace M = ⊤ := by simpa [hz'] using hc.sup_eq_top
    apply hne
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    have hx : x ∈ posSpace M := by rw [hp]; trivial
    have hx' := Module.End.mem_eigenspace_iff.mp hx
    simpa [involutionLin] using hx'
  have hle : finrank F (negSpace M) ≤ 3 := by omega
  interval_cases hn' : finrank F (negSpace M)
  · exact False.elim (hn rfl)
  · norm_num at hd
    exfalso
    apply h2
    linear_combination -hd
  · exact ⟨rfl, by omega⟩
  · norm_num at hd
    exfalso
    apply h2
    linear_combination -hd

/-- The negative and positive eigenspaces of an involution are complementary. -/
theorem involution_eigenspaces_isCompl (h2 : (2 : F) ≠ 0)
    (M : Matrix (Fin 3) (Fin 3) F) (hsq : M * M = 1) :
    IsCompl (Module.End.eigenspace (Matrix.toLin' M) (-1)) (Module.End.eigenspace (Matrix.toLin' M) 1) :=
  involution_isCompl h2 M hsq

/-- A nonidentity determinant-one involution in dimension three has eigenspace
 dimensions two and one. No restriction on characteristic three is needed. -/
theorem involution_eigenspace_finrank (h2 : (2 : F) ≠ 0)
    (M : Matrix (Fin 3) (Fin 3) F) (hsq : M * M = 1)
    (hne : M ≠ 1) (hdet : M.det = 1) :
    finrank F (Module.End.eigenspace (Matrix.toLin' M) (-1)) = 2 ∧
      finrank F (Module.End.eigenspace (Matrix.toLin' M) 1) = 1 :=
  dimensions h2 M hsq hne hdet

/-- An ordered basis with two negative eigenvectors followed by a positive eigenvector. -/
theorem exists_involution_eigenbasis (h2 : (2 : F) ≠ 0)
    (M : Matrix (Fin 3) (Fin 3) F) (hsq : M * M = 1)
    (hne : M ≠ 1) (hdet : M.det = 1) :
    ∃ b : Basis (Fin 3) F (Fin 3 → F),
      LinearMap.toMatrix b b (Matrix.toLin' M) = (standardInvolution F).val := by
  classical
  obtain ⟨hn, hp⟩ := dimensions h2 M hsq hne hdet
  let bn := Module.finBasisOfFinrankEq F (negSpace M) hn
  let bp := Module.finBasisOfFinrankEq F (posSpace M) hp
  let e := (negSpace M).prodEquivOfIsCompl (posSpace M) (involution_isCompl h2 M hsq)
  let b : Basis (Fin 3) F (Fin 3 → F) := ((bn.prod bp).map e).reindex finSumFinEquiv
  have hb0 : b 0 = (bn 0 : Fin 3 → F) := by
    simp only [b, Basis.reindex_apply, Basis.map_apply]
    change e ((bn.prod bp) (finSumFinEquiv.symm (Fin.castAdd 1 (0 : Fin 2)))) = _
    rw [finSumFinEquiv_symm_apply_castAdd]
    simp [e]
  have hb1 : b 1 = (bn 1 : Fin 3 → F) := by
    simp only [b, Basis.reindex_apply, Basis.map_apply]
    change e ((bn.prod bp) (finSumFinEquiv.symm (Fin.castAdd 1 (1 : Fin 2)))) = _
    rw [finSumFinEquiv_symm_apply_castAdd]
    simp [e]
  have hb2 : b 2 = (bp 0 : Fin 3 → F) := by
    simp only [b, Basis.reindex_apply, Basis.map_apply]
    change e ((bn.prod bp) (finSumFinEquiv.symm (Fin.natAdd 2 (0 : Fin 1)))) = _
    rw [finSumFinEquiv_symm_apply_natAdd]
    simp [e]
  have hf0 : involutionLin M (b 0) = (-1 : F) • b 0 := by
    rw [hb0]; exact Module.End.mem_eigenspace_iff.mp (bn 0).property
  have hf1 : involutionLin M (b 1) = (-1 : F) • b 1 := by
    rw [hb1]; exact Module.End.mem_eigenspace_iff.mp (bn 1).property
  have hf2 : involutionLin M (b 2) = (1 : F) • b 2 := by
    rw [hb2]; exact Module.End.mem_eigenspace_iff.mp (bp 0).property
  refine ⟨b, ?_⟩
  change LinearMap.toMatrix b b (involutionLin M) = _
  ext i j
  fin_cases j <;> fin_cases i <;>
    simp [LinearMap.toMatrix_apply, hf0, hf1, hf2, standardInvolution]

/-- A nonidentity determinant-one involution has the standard linear eigenbasis. -/
theorem exists_involution_conjugator (h2 : (2 : F) ≠ 0)
    (M : Matrix (Fin 3) (Fin 3) F) (hsq : M * M = 1)
    (hne : M ≠ 1) (hdet : M.det = 1) :
    ∃ P : GL (Fin 3) F,
      P.val * (standardInvolution F).val * (P⁻¹).val = M := by
  classical
  obtain ⟨b, hb⟩ := exists_involution_eigenbasis h2 M hsq hne hdet
  let s := Pi.basisFun F (Fin 3)
  let P : GL (Fin 3) F :=
    ⟨s.toMatrix b, b.toMatrix s,
      s.toMatrix_mul_toMatrix_flip b, b.toMatrix_mul_toMatrix_flip s⟩
  refine ⟨P, ?_⟩
  change s.toMatrix b * (standardInvolution F).val * b.toMatrix s = M
  rw [← hb, basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix]
  simp [s, LinearMap.toMatrix_eq_toMatrix']

end Matrix.SL3
end
