module

public import Theory.Representation.AlternatingFive.AmplifiedDeleted.Basic
public import Theory.Representation.TensorInvolutionDisplacement

/-!
# Disjoint subspaces in homogeneous deleted sums

Scalar multiplicity blocks preserve the amplification of every core subspace.
A permutation intertwiner sends it into the amplification of its permuted image.
Thus a subspace disjoint from its image contributes its dimension times the
multiplicity to displacement. The swap decomposition of a binary involution
provides such a subspace with dimension equal to its own displacement rank.

Source: Aschbacher--Smith D.3.9 and D.3.21, printed pp.199--201 and 204--207.
-/

@[expose] public noncomputable section

namespace Representation.AlternatingFive.AmplifiedDeleted
open Module BinaryOffender.NaturalTensor

/-- Pointwise amplification of a subspace of the simple deleted core. -/
def amplification (ι : Type*) (U : Submodule (ZMod 2) C) : Submodule (ZMod 2) (ι → C) where
  carrier := {v | ∀ i, v i ∈ U}
  zero_mem' := fun _ => U.zero_mem
  add_mem' hv hw i := U.add_mem (hv i) (hw i)
  smul_mem' c _ hv i := U.smul_mem c (hv i)

@[simp] theorem mem_amplification {ι : Type*} (U : Submodule (ZMod 2) C) (v : ι → C) :
    v ∈ amplification ι U ↔ ∀ i, v i ∈ U := Iff.rfl

/-- Amplification is the function space into the actual subspace. -/
def amplificationEquiv (ι : Type*) (U : Submodule (ZMod 2) C) :
    amplification ι U ≃ₗ[ZMod 2] (ι → U) where
  toFun v i := ⟨v.val i, v.property i⟩
  invFun v := ⟨fun i => (v i).val, fun i => (v i).property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finrank_amplification {ι : Type*} [Fintype ι] (U : Submodule (ZMod 2) C) :
    finrank (ZMod 2) (amplification ι U) = Fintype.card ι * finrank (ZMod 2) U := by
  rw [(amplificationEquiv ι U).finrank_eq, finrank_pi_fintype]
  simp

/-- Every disjoint core subspace gives its amplified displacement lower bound. -/
theorem amplified_disjoint_bound {ι : Type*} [Fintype ι]
    (T : Module.End (ZMod 2) (ι → C)) (p : Sym)
    (hT : ∀ (g : Alt) v, T (deletedSumAction ι g.val v) =
      deletedSumAction ι (p * g.val * p⁻¹) (T v))
    (U : Submodule (ZMod 2) C)
    (hU : Disjoint U (U.map (BinaryPermutation.coreRepresentation (Fin 5) p))) :
    Fintype.card ι * finrank (ZMod 2) U ≤ operatorFixedCodim T := by
  obtain ⟨a, ha⟩ := sum_intertwining_blocks T p hT
  have hmap : (amplification ι U).map T ≤
      amplification ι (U.map (BinaryPermutation.coreRepresentation (Fin 5) p)) := by
    rintro v ⟨w, hw, rfl⟩ i
    rw [ha]
    exact ⟨∑ j, a i j • w j, U.sum_mem (fun j _ => U.smul_mem _ (hw j)), rfl⟩
  have hd : Disjoint (amplification ι U) ((amplification ι U).map T) := by
    apply Submodule.disjoint_def.mpr
    intro v hv htv
    apply funext
    intro i
    exact Submodule.disjoint_def.mp hU (v i) (hv i) (hmap htv i)
  simpa only [finrank_amplification] using finrank_le_operatorFixedCodim_of_disjoint T _ hd

/-- An involution has a subspace disjoint from its image of dimension equal to
its displacement rank. This does not choose a basis or enumerate matrices. -/
theorem exists_disjoint_displacement_submodule
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (A : Module.End (ZMod 2) V) (hA : A * A = 1) :
    ∃ U : Submodule (ZMod 2) V,
      finrank (ZMod 2) U = operatorFixedCodim A ∧ Disjoint U (U.map A) := by
  obtain ⟨H, e, he⟩ := TensorInvolutionDisplacement.exists_swap_form A hA
  let R := LinearMap.range (A - 1)
  let f : R →ₗ[ZMod 2] V := e.toLinearMap.comp
    ((LinearMap.inl (ZMod 2) (R × R) H).comp (LinearMap.inl (ZMod 2) R R))
  have hf (r : R) : f r = e ((r, 0), 0) := rfl
  have hfi : Function.Injective f := by
    intro r s h
    exact congrArg (fun v : (R × R) × H => v.1.1) (e.injective h)
  refine ⟨LinearMap.range f, LinearMap.finrank_range_of_inj hfi, ?_⟩
  apply Submodule.disjoint_def.mpr
  rintro v ⟨r, rfl⟩ ⟨w, ⟨s, rfl⟩, hsr⟩
  have hs : e ((0, s), 0) = e ((r, 0), 0) := by
    simpa only [hf, he] using hsr
  have hr : r = 0 := (congrArg (fun v : (R × R) × H => v.1.1) (e.injective hs)).symm
  simp only [hr, map_zero]

/-- A permutation involution contributes its simple-core displacement in every
copy, even when the intertwiner mixes all displayed copies. -/
theorem amplified_involution_bound {ι : Type*} [Fintype ι]
    (T : Module.End (ZMod 2) (ι → C)) (p : Sym) (hp : p * p = 1)
    (hT : ∀ (g : Alt) v, T (deletedSumAction ι g.val v) =
      deletedSumAction ι (p * g.val * p⁻¹) (T v)) :
    Fintype.card ι * operatorFixedCodim (BinaryPermutation.coreRepresentation (Fin 5) p) ≤
      operatorFixedCodim T := by
  have hp' : BinaryPermutation.coreRepresentation (Fin 5) p *
      BinaryPermutation.coreRepresentation (Fin 5) p = 1 := by
    rw [← map_mul, hp, map_one]
  obtain ⟨U, hdim, hU⟩ := exists_disjoint_displacement_submodule _ hp'
  simpa only [hdim] using amplified_disjoint_bound T p hT U hU

end Representation.AlternatingFive.AmplifiedDeleted
