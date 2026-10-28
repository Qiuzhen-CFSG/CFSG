module
public import Theory.Representation.BinaryEndpointInduction.CoordinateCertificates
public import Theory.Representation.BinaryEndpointInduction.BlockLattice
public import Theory.Representation.BinaryEndpointInduction.MaskDisplacement
public import Theory.Representation.BinaryEndpointInduction.CosetTransitions
public import Theory.Representation.BinaryEndpointInduction.RowInvariant
public import Theory.Representation.BinaryEndpointInduction.FirstSpectralWord
public import Theory.Representation.BinaryEndpointInduction.SecondSpectralWord

/-!
# The exact kernels of endpoint quotients with small displacement

The literal spectral words force every invariant kernel into the checked
five-block lattice. Generator escapes and invertible eight-minors then
leave only the full kernel or the six-space/four-space kernel, respectively.
All four displacement matrices are transported through the same change of
basis as the group generators.
-/
public section
namespace BinaryEndpointInduction
open Matrix
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

private theorem kernel_invariant_of_intertwine
    {F ι U : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    [AddCommGroup U] [Module F U]
    (f : (ι → F) →ₗ[F] U) (B M N : Matrix ι ι F)
    (hMN : B*M=N*B) (hM : ∀ x, x ∈ f.ker → x ᵥ* M ∈ f.ker) :
    ∀ x, x ∈ (f.comp B.vecMulLinear).ker →
      x ᵥ* N ∈ (f.comp B.vecMulLinear).ker := by
  intro x hx
  change f ((x ᵥ* N) ᵥ* B)=0
  rw [vecMul_vecMul,←hMN,←vecMul_vecMul]
  exact hM _ hx

private theorem changed_row_displacement
    {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (B M N : Matrix ι ι F) (hMN : B*M=N*B) (i : ι) :
    (N i-Pi.single i 1) ᵥ* B=B i ᵥ* M-B i := by
  rw [sub_vecMul,single_one_vecMul]
  have he := congrArg (fun A : Matrix ι ι F => A i) hMN
  change B i ᵥ* M=N i ᵥ* B at he
  rw [he]
  rfl

private theorem changed_row_displacement_mem
    {F ι U : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    [AddCommGroup U] [Module F U]
    (f : (ι → F) →ₗ[F] U) (D : Submodule F U)
    (B M N : Matrix ι ι F) (hMN : B*M=N*B)
    (hmem : ∀ x, f (x ᵥ* M-x) ∈ D) (i : ι) :
    (f.comp B.vecMulLinear) (N i-Pi.single i 1) ∈ D := by
  change f ((N i-Pi.single i 1) ᵥ* B) ∈ D
  rw [changed_row_displacement B M N hMN]
  exact hmem _

private theorem spectral_algebra_member (dual : Bool)
    (A : Subalgebra (ZMod 2) (Matrix (Fin 45) (Fin 45) (ZMod 2)))
    (hA : ∀ i : Fin 2, generator dual i ∈ A) : spectral dual ∈ A := by
  cases dual
  · exact spectral_false_mem A hA
  · exact spectral_true_mem A hA

private theorem common_companion_intertwine (dual : Bool) :
    changeMatrix dual * spectral dual=companion false * changeMatrix dual := by
  have he : companion dual=companion false := by cases dual; rfl; exact companion_eq
  exact (spectral_intertwine dual).trans (congrArg (fun A => A*changeMatrix dual) he)

/-- Every quotient of the literal induced coordinates whose parabolic
movement fits in seven dimensions has exactly one of the two displayed
kernels in spectral coordinates. -/
theorem small_displacement_kernel
    (dual : Bool) (f : (Fin 45 → ZMod 2) →ₗ[ZMod 2] W)
    (hinv : ∀ k : Fin 2, ∀ x, x ∈ f.ker → x ᵥ* generator dual k ∈ f.ker)
    (D : Submodule (ZMod 2) W) [FiniteDimensional (ZMod 2) D]
    (hdim : Module.finrank (ZMod 2) D ≤ 7)
    (hmem : ∀ k : Fin 4, ∀ x : Fin 45 → ZMod 2,
      f (x ᵥ* inducedCosetMatrix dual ⟨k.val+2,by omega⟩-x) ∈ D) :
    ∃ mask : Fin 32,
      (f.comp (changeMatrix dual).vecMulLinear).ker=maskSubspace mask ∧
      (mask.val=31 ∨ mask.val=(if dual then 29 else 27)) := by
  let A := Algebra.adjoin (ZMod 2) (Set.range (generator dual))
  have hA (i : Fin 2) : generator dual i ∈ A := Algebra.subset_adjoin ⟨i,rfl⟩
  have hs := spectral_algebra_member dual A hA
  have hspec := row_invariant_of_mem_adjoin (generator dual) f.ker hinv hs
  have hc := kernel_invariant_of_intertwine f (changeMatrix dual)
    (spectral dual) (companion false) (common_companion_intertwine dual) hspec
  obtain ⟨mask,hmask⟩ := invariant_subspace_eq_maskSubspace
    (f.comp (changeMatrix dual).vecMulLinear).ker hc
  refine ⟨mask,hmask,mask_eq_of_small_displacement dual mask
    (f.comp (changeMatrix dual).vecMulLinear) hmask
    (fun k => kernel_invariant_of_intertwine f (changeMatrix dual)
      (generator dual k) (adaptedGenerator dual k) (generator_intertwine dual k) (hinv k))
    D hdim ?_⟩
  intro k i
  exact changed_row_displacement_mem f D (changeMatrix dual)
    (inducedCosetMatrix dual ⟨k.val+2,by omega⟩) (adaptedParabolic dual k)
    (parabolic_intertwine dual k) (hmem k) i
end BinaryEndpointInduction
