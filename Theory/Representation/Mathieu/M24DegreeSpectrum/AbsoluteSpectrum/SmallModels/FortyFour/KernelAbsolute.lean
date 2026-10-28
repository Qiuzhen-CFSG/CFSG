module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels.FortyFour.KernelAbsolute.Interface
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels.FortyFour.KernelAbsolute.Density
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels.FortyFour.KernelAbsolute.NativeMap

/-!
# Density transfer to the native Golay exterior kernel

The checked binary pair generates every 44-by-44 matrix. A nonzero linear map
intertwining this pair with the two native operators is therefore injective.
The proved dimension of the literal kernel makes it an equivalence, and scalar
extension of density proves absolute irreducibility. The native comparison map
is constructed from wedges of the actual Golay rows in `NativeMap`, which
proves its nonvanishing and both intertwining identities. Applying the transfer
to this map proves absolute irreducibility of the fixed native kernel.

Source context: James, The modular characters of the Mathieu groups,
J. Algebra 27 (1973), 57--111; GM02 Proposition 5.1, manuscript p.17.
-/

@[expose] public noncomputable section
open Sporadic.Mathieu
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels.FortyFour
namespace KernelAbsolute

private def preserving (W : Submodule (ZMod 2) Data.Space) :
    Subalgebra (ZMod 2) Data.Mat where
  carrier := {M | ∀ x ∈ W, M.mulVec x ∈ W}
  zero_mem' := by intro x _; simp
  one_mem' := by intro x hx; simpa using hx
  add_mem' := by
    intro M N hM hN x hx
    simpa only [Matrix.add_mulVec] using W.add_mem (hM x hx) (hN x hx)
  mul_mem' := by
    intro M N hM hN x hx
    simpa only [← Matrix.mulVec_mulVec] using hM _ (hN x hx)
  algebraMap_mem' := by
    intro r x hx
    simpa only [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec,
      Matrix.one_mulVec] using W.smul_mem r hx

private theorem injective_of_pair_intertwiner {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V]
    (T : Data.Space →ₗ[ZMod 2] V) (hT : T ≠ 0)
    (f : Fin 2 → Module.End (ZMod 2) V)
    (h : ∀ j v, T ((Data.matrix j).mulVec v) = f j (T v)) :
    Function.Injective T := by
  apply LinearMap.ker_eq_bot.mp
  by_contra hn
  have hfull : preserving T.ker = ⊤ := by
    apply Density.full
    intro j x hx
    change T ((Data.matrix j).mulVec x) = 0
    rw [h, LinearMap.mem_ker.mp hx, map_zero]
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra hzero
    push Not at hzero
    exact hx0 (funext hzero)
  have hi1 : x i = 1 := by
    have hb : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide +kernel
    exact (hb (x i)).resolve_left hi
  apply hT
  apply LinearMap.ext
  intro y
  have hm : Matrix.vecMulVec y (Pi.single i 1) ∈ preserving T.ker := by
    rw [hfull]
    trivial
  have hy := hm x hx
  simpa [Matrix.vecMulVec_mulVec, hi1] using hy

private theorem dense_of_coordinates {G V : Type*} [Monoid G]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (g : Fin 2 → G)
    (E : V ≃ₗ[ZMod 2] Data.Space)
    (h : ∀ (j : Fin 2) (v : V), E (ρ (g j) v) = (Data.matrix j).mulVec (E v)) :
    Algebra.adjoin (ZMod 2) (Set.range ρ) = ⊤ := by
  let P := Algebra.adjoin (ZMod 2) (Set.range ρ)
  let L : Data.Mat ≃ₐ[ZMod 2] Module.End (ZMod 2) V :=
    Matrix.toLinAlgEquiv'.trans (E.symm.conjAlgEquiv (ZMod 2))
  have hL (j : Fin 2) : L (Data.matrix j) = ρ (g j) := by
    apply LinearMap.ext
    intro v
    change E.symm ((Data.matrix j).mulVec (E v)) = ρ (g j) v
    rw [← h]
    exact E.symm_apply_apply _
  have hfull : P.comap L.toAlgHom = ⊤ := by
    apply Density.full
    intro j
    change L (Data.matrix j) ∈ P
    rw [hL]
    exact Algebra.subset_adjoin (Set.mem_range_self (g j))
  apply top_unique
  intro f _
  have hf : L.symm f ∈ P.comap L.toAlgHom := by rw [hfull]; trivial
  change L (L.symm f) ∈ P at hf
  simpa only [AlgEquiv.apply_symm_apply] using hf

private theorem absolute_of_map {G V : Type*} [Monoid G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (g : Fin 2 → G)
    (hdV : Module.finrank (ZMod 2) V = 44)
    (T : Data.Space →ₗ[ZMod 2] V) (hT : T ≠ 0)
    (h : ∀ (j : Fin 2) (v : Data.Space),
      T ((Data.matrix j).mulVec v) = ρ (g j) (T v)) :
    IsAbsolutelyIrreducible ρ := by
  have hinj := injective_of_pair_intertwiner T hT (fun j => ρ (g j)) h
  have hd : Module.finrank (ZMod 2) Data.Space = Module.finrank (ZMod 2) V := by
    rw [hdV]
    simp [Data.Space]
  let E : Data.Space ≃ₗ[ZMod 2] V :=
    LinearEquiv.ofBijective T ⟨hinj,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp hinj⟩
  have hdense : Algebra.adjoin (ZMod 2) (Set.range ρ) = ⊤ := by
    apply dense_of_coordinates ρ g E.symm
    intro j v
    apply E.injective
    rw [E.apply_symm_apply]
    change ρ (g j) v = T ((Data.matrix j).mulVec (E.symm v))
    rw [h]
    change ρ (g j) v = ρ (g j) (E (E.symm v))
    rw [E.apply_symm_apply]
  let : Nontrivial V := E.injective.nontrivial
  let : IsIrreducible ρ := irreducible_of_jacobson_density_surjective _ hdense
  apply (isAbsolutelyIrreducible_iff_surjective ρ).mpr
  exact surjective_of_jacobson_density_surjective_rep _ hdense

/-- The exact native comparison needed to consume the checked density certificate. -/
theorem kernel_dense_of_native_coordinates
    (E : Kernel ≃ₗ[ZMod 2] Data.Space)
    (h : ∀ (j : Fin 2) (v : Kernel),
      E (kernelRepresentation (nativeGenerator j) v) = (Data.matrix j).mulVec (E v)) :
    Algebra.adjoin (ZMod 2) (Set.range kernelRepresentation) = ⊤ :=
  dense_of_coordinates kernelRepresentation nativeGenerator E h

end KernelAbsolute

/-- Conditional native application. The coordinate identities must still be proved. -/
theorem kernel_absolute_of_native_coordinates
    (E : Kernel ≃ₗ[ZMod 2] KernelAbsolute.Data.Space)
    (h : ∀ (j : Fin 2) (v : Kernel),
      E (kernelRepresentation (KernelAbsolute.nativeGenerator j) v) =
        (KernelAbsolute.Data.matrix j).mulVec (E v)) :
    IsAbsolutelyIrreducible kernelRepresentation := by
  let : Nontrivial Kernel := E.symm.injective.nontrivial
  let : IsIrreducible kernelRepresentation :=
    irreducible_of_jacobson_density_surjective _
      (KernelAbsolute.kernel_dense_of_native_coordinates E h)
  apply (isAbsolutelyIrreducible_iff_surjective kernelRepresentation).mpr
  exact surjective_of_jacobson_density_surjective_rep _
    (KernelAbsolute.kernel_dense_of_native_coordinates E h)

/-- A nonzero comparison map suffices; density proves its injectivity, and the
already proved dimension of the native kernel proves its surjectivity. -/
theorem kernel_absolute_of_native_map
    (T : KernelAbsolute.Data.Space →ₗ[ZMod 2] Kernel) (hT : T ≠ 0)
    (h : ∀ (j : Fin 2) (v : KernelAbsolute.Data.Space),
      T ((KernelAbsolute.Data.matrix j).mulVec v) =
        kernelRepresentation (KernelAbsolute.nativeGenerator j) (T v)) :
    IsAbsolutelyIrreducible kernelRepresentation :=
  KernelAbsolute.absolute_of_map kernelRepresentation KernelAbsolute.nativeGenerator
    finrank_kernel T hT h

/-- The literal degree-44 Golay exterior contraction kernel is absolutely
irreducible. This discharges the absolute-irreducibility premise of the native
binary degree-44 pair construction. -/
theorem kernel_isAbsolutelyIrreducible :
    IsAbsolutelyIrreducible kernelRepresentation :=
  kernel_absolute_of_native_map KernelAbsolute.NativeMap.comparisonMap
    KernelAbsolute.NativeMap.comparisonMap_ne_zero
    KernelAbsolute.NativeMap.comparisonMap_action

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels.FortyFour
