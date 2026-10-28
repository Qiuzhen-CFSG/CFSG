module

public import Theory.SpecificGroups.PSL4Three.TwoLocal.StandardInvolution
public import Theory.SpecificGroups.PSL4Three.LocalThree.Model
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Basis.Fin

/-!
# A two-plus-two eigenbasis over F₃

A trace-zero involution on F₃⁴ has complementary positive and negative
eigenspaces, both of dimension two. Joining their bases gives a genuine
GL₄(3) conjugator to diag(-1,-1,1,1).

Adapted from the existing linear eigenbasis proof for the field-nine unitary
model, with the field replaced by F₃; this is ordinary linear algebra.
Source application: Aschbacher–Smith, Theorem 0.1.2(4), printed p.4,
repeated as Theorem 0.1.1(4), printed p.482 of `refs/quasithin.pdf`.
-/

open Matrix Module Submodule
open scoped Matrix

public section
namespace Matrix.PSL4Three.LocalThree.FourCentralizer

private abbrev F := ZMod 3

open Matrix.PSL4Three.TwoLocal

/-- The split involution in the full linear group. -/
@[expose] def splitInvolutionGL : GL (Fin 4) (ZMod 3) :=
  ⟨standardInvolutionMatrix, standardInvolutionMatrix, by decide, by decide⟩

private def involutionLin (M : Matrix (Fin 4) (Fin 4) F) : Module.End F (Fin 4 → F) :=
  Matrix.toLin' M

private def negSpace (M : Matrix (Fin 4) (Fin 4) F) : Submodule F (Fin 4 → F) :=
  (involutionLin M).eigenspace (-1)

private def posSpace (M : Matrix (Fin 4) (Fin 4) F) : Submodule F (Fin 4 → F) :=
  (involutionLin M).eigenspace 1

private theorem involution_isCompl
    (M : Matrix (Fin 4) (Fin 4) F) (hsq : M * M = 1) :
    IsCompl (negSpace M) (posSpace M) := by
  have h2 : (2 : F) ≠ 0 := by decide
  let f := involutionLin M
  have hf : f * f = 1 := by
    apply LinearMap.ext
    intro x
    change M *ᵥ (M *ᵥ x) = x
    calc
      M *ᵥ (M *ᵥ x) = (M * M) *ᵥ x := Matrix.mulVec_mulVec x M M
      _ = x := by rw [hsq]; simp
  have hfx (x : Fin 4 → F) : f (f x) = x := by
    simpa [Module.End.mul_apply] using congrArg (fun g : Module.End F (Fin 4 → F) => g x) hf
  have hsum : negSpace M ⊔ posSpace M = ⊤ := by
    apply top_unique
    intro x hx
    let u : Fin 4 → F := (2 : F)⁻¹ • (x - f x)
    let v : Fin 4 → F := (2 : F)⁻¹ • (x + f x)
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
      funext i
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

private theorem trace_involution
    (M : Matrix (Fin 4) (Fin 4) F) (hsq : M * M = 1) :
    M.trace = -(finrank F (negSpace M) : F) + finrank F (posSpace M) := by
  let e := (negSpace M).prodEquivOfIsCompl (posSpace M) (involution_isCompl M hsq)
  let g : Module.End F (negSpace M × posSpace M) :=
    LinearMap.prodMap ((-1 : F) • (1 : Module.End F (negSpace M))) 1
  have he (x : negSpace M × posSpace M) : involutionLin M (e x) = e (g x) := by
    have hn := (Module.End.mem_eigenspace_iff.mp x.1.property)
    have hp := (Module.End.mem_eigenspace_iff.mp x.2.property)
    change involutionLin M ((x.1 : Fin 4 → F) + x.2) =
      (-1 : F) • (x.1 : Fin 4 → F) + x.2
    rw [map_add, hn, hp, one_smul]
  have hf : involutionLin M = e.conj g := by
    apply LinearMap.ext
    intro x
    simpa using he (e.symm x)
  calc
    M.trace = LinearMap.trace F _ (involutionLin M) := by simp [involutionLin]
    _ = LinearMap.trace F _ g := by rw [hf, LinearMap.trace_conj']
    _ = -(finrank F (negSpace M) : F) + finrank F (posSpace M) := by
      simp [g, LinearMap.trace_prodMap']

private theorem dimensions
    (M : Matrix (Fin 4) (Fin 4) F) (hsq : M * M = 1) (htrace : M.trace = 0) :
    finrank F (negSpace M) = 2 ∧ finrank F (posSpace M) = 2 := by
  have hc := involution_isCompl M hsq
  have hsum : finrank F (negSpace M) + finrank F (posSpace M) = 4 := by
    simpa using Submodule.finrank_add_eq_of_isCompl hc
  have ht : -(finrank F (negSpace M) : F) + finrank F (posSpace M) = 0 :=
    (trace_involution M hsq).symm.trans htrace
  have hp : finrank F (posSpace M) = 4 - finrank F (negSpace M) := by omega
  rw [hp] at ht
  have hn : finrank F (negSpace M) ≤ 4 := by omega
  -- Among dimensions zero through four, only two satisfies the trace equation in F₃.
  interval_cases hn' : finrank F (negSpace M)
  all_goals first
    | exact ⟨rfl, by omega⟩
    | exfalso; revert ht; decide

private theorem exists_involution_eigenbasis
    (M : Matrix (Fin 4) (Fin 4) F) (hsq : M * M = 1)
    (htrace : M.trace = 0) :
    ∃ b : Basis (Fin 4) F (Fin 4 → F),
      LinearMap.toMatrix b b (Matrix.toLin' M) = standardInvolutionMatrix := by
  classical
  obtain ⟨hn, hp⟩ := dimensions M hsq htrace
  let bn := Module.finBasisOfFinrankEq F (negSpace M) hn
  let bp := Module.finBasisOfFinrankEq F (posSpace M) hp
  let e := (negSpace M).prodEquivOfIsCompl (posSpace M) (involution_isCompl M hsq)
  let b : Basis (Fin 4) F (Fin 4 → F) := ((bn.prod bp).map e).reindex finSumFinEquiv
  have hb0 : b 0 = (bn 0 : Fin 4 → F) := by
    simp only [b, Basis.reindex_apply, Basis.map_apply]
    change e ((bn.prod bp) (finSumFinEquiv.symm (Fin.castAdd 2 (0 : Fin 2)))) = _
    rw [finSumFinEquiv_symm_apply_castAdd]
    simp [e]
  have hb1 : b 1 = (bn 1 : Fin 4 → F) := by
    simp only [b, Basis.reindex_apply, Basis.map_apply]
    change e ((bn.prod bp) (finSumFinEquiv.symm (Fin.castAdd 2 (1 : Fin 2)))) = _
    rw [finSumFinEquiv_symm_apply_castAdd]
    simp [e]
  have hb2 : b 2 = (bp 0 : Fin 4 → F) := by
    simp only [b, Basis.reindex_apply, Basis.map_apply]
    change e ((bn.prod bp) (finSumFinEquiv.symm (Fin.natAdd 2 (0 : Fin 2)))) = _
    rw [finSumFinEquiv_symm_apply_natAdd]
    simp [e]
  have hb3 : b 3 = (bp 1 : Fin 4 → F) := by
    simp only [b, Basis.reindex_apply, Basis.map_apply]
    change e ((bn.prod bp) (finSumFinEquiv.symm (Fin.natAdd 2 (1 : Fin 2)))) = _
    rw [finSumFinEquiv_symm_apply_natAdd]
    simp [e]
  have hf0 : involutionLin M (b 0) = (-1 : F) • b 0 := by
    rw [hb0]; exact Module.End.mem_eigenspace_iff.mp (bn 0).property
  have hf1 : involutionLin M (b 1) = (-1 : F) • b 1 := by
    rw [hb1]; exact Module.End.mem_eigenspace_iff.mp (bn 1).property
  have hf2 : involutionLin M (b 2) = (1 : F) • b 2 := by
    rw [hb2]; exact Module.End.mem_eigenspace_iff.mp (bp 0).property
  have hf3 : involutionLin M (b 3) = (1 : F) • b 3 := by
    rw [hb3]; exact Module.End.mem_eigenspace_iff.mp (bp 1).property
  refine ⟨b, ?_⟩
  change LinearMap.toMatrix b b (involutionLin M) = _
  apply Matrix.ext
  intro i j
  fin_cases j <;> fin_cases i <;>
    simp [LinearMap.toMatrix_apply, hf0, hf1, hf2, hf3, standardInvolutionMatrix]

/-- Every trace-zero linear involution over F₃ is
conjugate to `diag(-1,-1,1,1)`. -/
theorem exists_linear_conjugator_of_trace_zero
    (M : GL (Fin 4) (ZMod 3)) (hsq : M ^ 2 = 1) (htrace : Matrix.trace M.val = 0) :
    ∃ P : GL (Fin 4) (ZMod 3), P * splitInvolutionGL * P⁻¹ = M := by
  classical
  have hsq' : M.val * M.val = 1 := by
    simpa only [pow_two, Units.val_mul, Units.val_one] using congrArg Units.val hsq
  obtain ⟨b, hb⟩ := exists_involution_eigenbasis M.val hsq' htrace
  let s := Pi.basisFun F (Fin 4)
  let P : GL (Fin 4) F :=
    ⟨s.toMatrix b, b.toMatrix s,
      s.toMatrix_mul_toMatrix_flip b, b.toMatrix_mul_toMatrix_flip s⟩
  refine ⟨P, Units.ext ?_⟩
  change s.toMatrix b * standardInvolutionMatrix * b.toMatrix s = M.val
  rw [← hb, basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix]
  simp [s, LinearMap.toMatrix_eq_toMatrix']

end Matrix.PSL4Three.LocalThree.FourCentralizer
end
