module

public import Theory.Representation.BinaryPermutation.SixCoreStabilizer
public import Theory.GroupTheory.PResidual.PrimeToTransport
public import Theory.GroupTheory.NormalSubgroupCoreQuotient
public import Theory.GroupTheory.SylowKernelCore
public import Theory.GroupTheory.PCoreImage

/-!
# Movement by the core of a six-letter vector stabilizer residual

The stabilizer of any nonconstant vector in the five-dimensional binary
augmentation core is S₄. A complementary 3-cycle lies in its literal
O^{3′}; its commutator with a double transposition lies in O₂(O^{3′}).
On an explicit even word this commutator moves the 3-cycle displacement.
Even-permutation transport and complementation give the result for every
nonconstant vector, retaining the original core rather than its natural
four-dimensional quotient.

The consumer is the A₆-block contradiction in Aschbacher–Smith 13.4.8,
printed p.904: [V₃,O₂(L₁)] is nontrivial for V₃=[V,L₁]. Only the small
permutation and binary-word identities use kernel-checked computation.
-/

public noncomputable section

open Subgroup
open scoped commutatorElement
namespace BinaryPermutation.SixCoreResidualMovement
open Theory.SpecificGroups.SymmetricSix
abbrev A := alternatingGroup (Fin 6)
abbrev W := core (Fin 6)
abbrev rho := alternatingCoreRepresentation (Fin 6)
abbrev S (w : W) := SixCoreStabilizer.stabilizer w
private def pair : W := ⟨![1,1,0,0,0,0],by rw [mem_core];decide⟩
private theorem pair_stabilizer : S pair = a6DuadStabilizer := by
  ext a
  change rho a pair = pair ↔ a.val ∈ duadStabilizer
  revert a
  decide +kernel
private noncomputable def e : Equiv.Perm (Fin 4) ≃* S pair :=
  a6DuadModelEquiv.trans (MulEquiv.subgroupCongr pair_stabilizer.symm)
private def a0 : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 1 2
private def c0 : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3
private noncomputable def a : S pair := e a0
private noncomputable def c : S pair := e c0
private noncomputable def b : S pair := ⁅a,c⁆
private theorem a_cubic : a ^ 3 = 1 := by
  change e a0 ^ 3 = 1
  rw [← map_pow, show a0 ^ 3 = 1 by decide, map_one]
private theorem c_core : c ∈ pCore 2 (S pair) := by
  rw [← pCore_map_iso 2 e]
  apply mem_map_of_mem
  rw [← DuadCalculation.core_eq, DuadCalculation.core_mem_iff]
  decide
private theorem a_residual : a ∈ primeToResidual 3 (S pair) :=
  mem_primeToResidual_of_pow (n := 1) a_cubic
private theorem b_core : b ∈ (primeToResidual 3 (S pair)).pCoreIn 2 := by
  have hbR : b ∈ primeToResidual 3 (S pair) :=
    commutator_le_left _ _ (commutator_mem_commutator a_residual (mem_top c))
  have hbC : b ∈ pCore 2 (S pair) :=
    commutator_le_right _ _ (commutator_mem_commutator (mem_top a) c_core)
  refine ⟨⟨b,hbR⟩,?_,rfl⟩
  rw [pCore_eq_comap_of_normal]
  exact hbC
private def u : W := ⟨![1,0,1,0,0,0],by rw [mem_core];decide⟩
private theorem movement : rho b.val (rho a.val u - u) ≠ rho a.val u - u := by
  intro h
  have hh := congrArg (fun v : W => v.val 2) h
  change (0 : ZMod 2) = 1 at hh
  exact zero_ne_one hh

private theorem stabilizer_complement (w : W) : S (w + sixCoreConstant) = S w := by
  ext g
  change rho g (w + sixCoreConstant) = w + sixCoreConstant ↔ rho g w = w
  rw [map_add,sixCoreConstant_fixed,add_left_inj]

private local instance : MulAction A W where
  smul g w := rho g w
  one_smul w := by change rho 1 w = w; rw [map_one]; rfl
  mul_smul g h w := by change rho (g*h) w = rho g (rho h w); rw [map_mul]; rfl

private theorem stabilizer_conjugate (g : A) (w : W) :
    (S w).map (MulAut.conj g).toMonoidHom = S (rho g w) :=
  (MulAction.stabilizer_smul_eq_stabilizer_map_conj g w).symm

private theorem conjugate_action (g x : A) (v : W) :
    rho (MulAut.conj g x) (rho g v) = rho g (rho x v) := by
  change rho (g*x*g⁻¹) (rho g v) = _
  rw [← Module.End.mul_apply,← map_mul]
  simp only [mul_assoc,inv_mul_cancel,mul_one,map_mul,Module.End.mul_apply]

private theorem rho_injective (g : A) : Function.Injective (rho g) := by
  intro v w h
  have hh := congrArg (rho g⁻¹) h
  simpa only [← Module.End.mul_apply,← map_mul,inv_mul_cancel,map_one,
    Module.End.one_apply] using hh

/-- The two-core of the literal cubic residual moves its displacement space. -/
theorem exists_residual_core_movement (w : W) (hfix : ¬ ∀ g : A, rho g w = w) :
    ∃ x y : S w, x ∈ primeToResidual 3 (S w) ∧
      y ∈ (primeToResidual 3 (S w)).pCoreIn 2 ∧
      ∃ v : W, rho y.val (rho x.val v - v) ≠ rho x.val v - v := by
  have hw := not_or.mp ((not_congr (sixCore_fixed_iff w)).mp hfix)
  have step (w₀ : W) (hs : S w₀ = S pair) (g : A) (hg : rho g w₀ = w) :
      ∃ x y : S w, x ∈ primeToResidual 3 (S w) ∧
        y ∈ (primeToResidual 3 (S w)).pCoreIn 2 ∧
        ∃ v : W, rho y.val (rho x.val v - v) ≠ rho x.val v - v := by
    have he := stabilizer_conjugate g w₀
    rw [hg] at he
    let f : S pair ≃* S w := (MulEquiv.subgroupCongr hs.symm).trans
      (((S w₀).equivMapOfInjective (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr he))
    have hf (x : S pair) : (f x).val = MulAut.conj g x.val := rfl
    refine ⟨f a,f b,?_,?_,rho g u,?_⟩
    · rw [← map_primeToResidual f]
      exact mem_map_of_mem f.toMonoidHom a_residual
    · rw [← map_primeToResidual f,← map_pCoreIn_of_injective 2 _ _ f.injective]
      exact mem_map_of_mem f.toMonoidHom b_core
    · rw [hf,hf,conjugate_action,← map_sub,conjugate_action]
      exact fun hh => movement (rho_injective g hh)
  rcases sixCore_paired_orbits pair w (by decide) (by decide) hw.1 hw.2 with
    ⟨g,hg⟩ | ⟨g,hg⟩
  · exact step pair rfl g hg
  · exact step (pair + sixCoreConstant) (stabilizer_complement pair) g hg

/-- The full stabilizer in A₆ of a nonconstant core vector is S₄. -/
theorem stabilizer_equiv (w : W) (hfix : ¬ ∀ g : A, rho g w = w) :
    Nonempty (S w ≃* Equiv.Perm (Fin 4)) := by
  have hw := not_or.mp ((not_congr (sixCore_fixed_iff w)).mp hfix)
  have step (w₀ : W) (hs : S w₀ = S pair) (g : A) (hg : rho g w₀ = w) :
      Nonempty (S w ≃* Equiv.Perm (Fin 4)) := by
    have he := stabilizer_conjugate g w₀
    rw [hg] at he
    exact ⟨((MulEquiv.subgroupCongr he.symm).trans
      (((S w₀).equivMapOfInjective (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).symm.trans (MulEquiv.subgroupCongr hs))).trans e.symm⟩
  rcases sixCore_paired_orbits pair w (by decide) (by decide) hw.1 hw.2 with h | h
  · exact step pair rfl h.choose h.choose_spec
  · exact step (pair + sixCoreConstant) (stabilizer_complement pair) h.choose h.choose_spec

end BinaryPermutation.SixCoreResidualMovement
