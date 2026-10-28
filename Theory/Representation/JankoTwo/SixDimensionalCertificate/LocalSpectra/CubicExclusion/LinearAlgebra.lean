module

public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Algebra.DirectSum.LinearMap
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Tactic.NormNum

/-!
# Cubic operators on a plane

A nonidentity cubic operator of determinant one on a characteristic-two plane
has each primitive cubic eigenvalue once, and trace one. Separability gives an
actual eigenspace decomposition; a collected eigenbasis computes its determinant.
The restriction lemma also computes dimensions inside invariant subspaces.

These linear-algebra calculations are used by the literal J₂ triangle action
in `XSpaces` and the ambient cubic multiplicity calculation in `CubicExclusion`.
Source application: Aschbacher–Smith K.4.5, printed p.460; see ../../Source.md.
-/

@[expose] public noncomputable section
open Polynomial Module
open scoped DirectSum BigOperators
namespace Representation.JankoTwo.SixDimensionalCertificate.LocalSpectra.CubicExclusion
variable {E V : Type*} [Field E] [AddCommGroup V] [Module E V]

lemma power_eigenspaces_internal [FiniteDimensional E V] [IsAlgClosed E]
    (f : Module.End E V) {n : ℕ} [NeZero n] (hn : (n : E) ≠ 0)
    (hf : f ^ n = 1) {z : E} (hz : IsPrimitiveRoot z n) :
    DirectSum.IsInternal (fun i : Fin n => f.eigenspace (z ^ i.val)) := by
  classical
  have hs : f.IsSemisimple := by
    apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
      (p := (X : E[X]) ^ n - 1)
    · exact (X_pow_sub_one_separable_iff.mpr hn).squarefree
    · simp [hf]
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · exact f.eigenspaces_iSupIndep.comp
      (fun i j h => Fin.ext (hz.pow_inj i.isLt j.isLt h))
  · apply top_unique
    rw [← hs.iSup_eigenspace_eq_top]
    refine iSup_le fun a => ?_
    by_cases ha : f.eigenspace a = ⊥
    · simp [ha]
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ha
    have he : f.HasEigenvector a v := ⟨hv, hv0⟩
    have hp : a ^ n = 1 := by
      apply smul_left_injective E hv0
      simpa [hf] using (he.pow_apply n).symm
    obtain ⟨i, hi, rfl⟩ := hz.eq_pow_of_pow_eq_one hp
    exact le_iSup (fun i : Fin n => f.eigenspace (z ^ i.val)) ⟨i, hi⟩

lemma finrank_of_internal {I : Type*} [Fintype I] [DecidableEq I]
    [FiniteDimensional E V] (S : I → Submodule E V) (hS : DirectSum.IsInternal S) :
    Module.finrank E V = ∑ i, Module.finrank E (S i) := by
  have h := (LinearEquiv.ofBijective (DirectSum.coeLinearMap S) hS).finrank_eq
  simpa only [Module.finrank_directSum] using h.symm

private lemma determinant_of_eigenspaces {I : Type*} [Fintype I] [DecidableEq I]
    [FiniteDimensional E V] (f : Module.End E V) (a : I → E)
    (h : DirectSum.IsInternal (fun i => f.eigenspace (a i))) :
    LinearMap.det f = ∏ i, a i ^ Module.finrank E (f.eigenspace (a i)) := by
  classical
  let b := h.collectedBasis (fun i => Module.finBasis E (f.eigenspace (a i)))
  have he (i) : f (b i) = a i.1 • b i :=
    Module.End.mem_eigenspace_iff.mp (h.collectedBasis_mem _ i)
  have hm : LinearMap.toMatrix b b f = Matrix.diagonal (fun i => a i.1) := by
    ext i j
    by_cases hij : i = j <;> simp [LinearMap.toMatrix_apply, he, hij]
  rw [← LinearMap.det_toMatrix b, hm, Matrix.det_diagonal, Fintype.prod_sigma]
  simp

private lemma trace_of_eigenspaces {I : Type*} [Fintype I] [DecidableEq I]
    [FiniteDimensional E V] (f : Module.End E V) (a : I → E)
    (h : DirectSum.IsInternal (fun i => f.eigenspace (a i))) :
    LinearMap.trace E V f = ∑ i, (Module.finrank E (f.eigenspace (a i)) : E) * a i := by
  classical
  let hf (i) : Set.MapsTo f (f.eigenspace (a i)) (f.eigenspace (a i)) := by
    intro v hv
    rw [Module.End.mem_eigenspace_iff.mp hv]
    exact (f.eigenspace (a i)).smul_mem _ hv
  rw [LinearMap.trace_eq_sum_trace_restrict h hf]
  apply Finset.sum_congr rfl
  intro i _
  have he : f.restrict (hf i) = a i • LinearMap.id := by
    ext v
    exact Module.End.mem_eigenspace_iff.mp v.property
  rw [he, map_smul, LinearMap.trace_id, smul_eq_mul, mul_comm]

private lemma scalar_of_full_eigenspace [FiniteDimensional E V]
    (f : Module.End E V) (a : E)
    (h : Module.finrank E (f.eigenspace a) = Module.finrank E V) :
    f = a • LinearMap.id := by
  have ht : f.eigenspace a = ⊤ := Submodule.eq_top_of_finrank_eq h
  ext v
  exact Module.End.mem_eigenspace_iff.mp (show v ∈ f.eigenspace a by rw [ht]; trivial)

lemma cubic_plane [FiniteDimensional E V] [IsAlgClosed E] [CharP E 2]
    (f : Module.End E V) (hdim : Module.finrank E V = 2)
    (hf : f ^ 3 = 1) (hdet : LinearMap.det f = 1) (hne : f ≠ 1)
    {z : E} (hz : IsPrimitiveRoot z 3) :
    Module.finrank E (f.eigenspace z) = 1 ∧
    Module.finrank E (f.eigenspace (z ^ 2)) = 1 ∧ LinearMap.trace E V f = 1 := by
  have hn : (3 : E) ≠ 0 := (CharP.cast_eq_zero_iff E 2 3).not.mpr (by decide)
  have hs := power_eigenspaces_internal f hn hf hz
  have hd := finrank_of_internal _ hs
  have hp := determinant_of_eigenspaces f _ hs
  have ht := trace_of_eigenspaces f _ hs
  let m : E → ℕ := fun a => Module.finrank E (f.eigenspace a)
  change Module.finrank E V = ∑ j : Fin 3, m (z ^ j.val) at hd
  change LinearMap.det f = ∏ j : Fin 3, (z ^ j.val) ^ m (z ^ j.val) at hp
  change LinearMap.trace E V f = ∑ j : Fin 3, (m (z ^ j.val) : E) * z ^ j.val at ht
  norm_num [Fin.sum_univ_three, Fin.prod_univ_three, hdim, hdet] at hd hp ht
  dsimp only [m] at hd hp ht
  have h0 : Module.finrank E (f.eigenspace 1) ≠ 2 := by
    intro h
    apply hne
    change f = LinearMap.id
    simpa using scalar_of_full_eigenspace f 1 (h.trans hdim.symm)
  have h1 : Module.finrank E (f.eigenspace z) ≤ 1 := by
    by_contra h
    have hm : Module.finrank E (f.eigenspace z) = 2 := by omega
    have he := scalar_of_full_eigenspace f z (hm.trans hdim.symm)
    rw [he, LinearMap.det_smul, LinearMap.det_id, mul_one, hdim] at hdet
    exact hz.pow_ne_one_of_pos_of_lt (by decide) (by decide) hdet
  have h2 : Module.finrank E (f.eigenspace (z ^ 2)) ≤ 1 := by
    by_contra h
    have hm : Module.finrank E (f.eigenspace (z ^ 2)) = 2 := by omega
    have he := scalar_of_full_eigenspace f (z ^ 2) (hm.trans hdim.symm)
    rw [he, LinearMap.det_smul, LinearMap.det_id, mul_one, hdim, ← pow_mul] at hdet
    have hh := (hz.pow_eq_one_iff_dvd 4).mp hdet
    norm_num at hh
  have hm1 : Module.finrank E (f.eigenspace z) = 1 := by
    by_contra h
    have hzero : Module.finrank E (f.eigenspace z) = 0 := by omega
    have hone : Module.finrank E (f.eigenspace (z ^ 2)) = 1 := by omega
    rw [hzero, hone, pow_zero, pow_one, one_mul] at hp
    exact hz.pow_ne_one_of_pos_of_lt (by decide) (by decide) hp.symm
  have hm2 : Module.finrank E (f.eigenspace (z ^ 2)) = 1 := by
    by_contra h
    have hzero : Module.finrank E (f.eigenspace (z ^ 2)) = 0 := by omega
    rw [hm1, hzero, pow_zero, pow_one, mul_one] at hp
    exact hz.ne_one (by decide) hp.symm
  refine ⟨hm1, hm2, ?_⟩
  have hm0 : Module.finrank E (f.eigenspace 1) = 0 := by omega
  rw [hm0, hm1, hm2] at ht
  have hzsum := hz.geom_sum_eq_zero (by decide : 1 < 3)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one,
    zero_add] at hzsum
  have he : z + z ^ 2 = 1 := by
    apply add_left_cancel (a := (1 : E))
    simpa only [add_assoc, CharTwo.add_self_eq_zero] using hzsum
  simpa [he] using ht

lemma finrank_restrict_eigenspace [FiniteDimensional E V]
    (f : Module.End E V) (p : Submodule E V) (hp : ∀ v ∈ p, f v ∈ p) (a : E) :
    Module.finrank E (Module.End.eigenspace (f.restrict hp) a) =
      Module.finrank E (p ⊓ f.eigenspace a : Submodule E V) := by
  let e : Module.End.eigenspace (f.restrict hp) a ≃ₗ[E] (p ⊓ f.eigenspace a : Submodule E V) :=
    { toFun := fun v => ⟨v.val.val, v.val.property, by
        have h := Module.End.mem_eigenspace_iff.mp v.property
        exact Module.End.mem_eigenspace_iff.mpr (congrArg Subtype.val h)⟩
      invFun := fun v => ⟨⟨v.val, v.property.1⟩, by
        apply Module.End.mem_eigenspace_iff.mpr
        apply Subtype.ext
        exact Module.End.mem_eigenspace_iff.mp v.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact e.finrank_eq

lemma finrank_invariant_eq_sum [FiniteDimensional E V] [IsAlgClosed E]
    (f : Module.End E V) {n : ℕ} [NeZero n] (hn : (n : E) ≠ 0)
    (hf : f ^ n = 1) {z : E} (hz : IsPrimitiveRoot z n)
    (p : Submodule E V) (hp : ∀ v ∈ p, f v ∈ p) :
    Module.finrank E p = ∑ i : Fin n,
      Module.finrank E (p ⊓ f.eigenspace (z ^ i.val) : Submodule E V) := by
  have hr : (f.restrict hp) ^ n = 1 := by
    rw [Module.End.pow_restrict]
    ext v
    change (f ^ n) v.val = v.val
    rw [hf, Module.End.one_apply]
  have hd := finrank_of_internal _ (power_eigenspaces_internal (f.restrict hp) hn hr hz)
  simpa only [finrank_restrict_eigenspace] using hd

lemma eigenspace_one_nonidentity (a : E) (ha : a ≠ 1) :
    (1 : Module.End E V).eigenspace a = ⊥ := by
  apply bot_unique
  intro v hv
  have h := Module.End.mem_eigenspace_iff.mp hv
  change v = a • v at h
  by_contra hv0
  exact ha ((smul_left_injective E hv0) (h.symm.trans (one_smul E v).symm))

end Representation.JankoTwo.SixDimensionalCertificate.LocalSpectra.CubicExclusion
