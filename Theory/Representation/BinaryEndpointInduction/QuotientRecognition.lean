module
public import Theory.Representation.BinaryEndpointInduction.QuotientKernel
public import Theory.Representation.BinaryEndpointInduction.SurvivorModels
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Recognition of every nonzero small-displacement endpoint quotient

The original quotient map and the coordinate survivor projection have
exactly the same kernel. Their first-isomorphism equivalences therefore
give an explicit isomorphism, with an equation on every original vector.
No simplicity or semisimplicity of the target is assumed.
-/
public noncomputable section
namespace BinaryEndpointInduction
open Matrix
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

private theorem row_map_surjective_of_inverse
    {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (B I : Matrix ι ι F) (hIB : I*B=1) : Function.Surjective B.vecMulLinear := by
  intro x
  refine ⟨x ᵥ* I,?_⟩
  change (x ᵥ* I) ᵥ* B=x
  rw [vecMul_vecMul,hIB,vecMul_one]

private theorem comp_row_map_surjective
    {F ι U : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    [AddCommGroup U] [Module F U]
    (f : (ι → F) →ₗ[F] U) (hf : Function.Surjective f)
    (B I : Matrix ι ι F) (hIB : I*B=1) :
    Function.Surjective (f.comp B.vecMulLinear) :=
  hf.comp (row_map_surjective_of_inverse B I hIB)

private theorem mask_full : maskSubspace (31 : Fin 32)=⊤ := by
  apply top_unique
  intro x _ j hj
  have h : ∀ j : Fin 45, (31 : ℕ).testBit (coordinateBlock j).val=true := by decide +kernel
  change (31 : ℕ).testBit (coordinateBlock j).val=false at hj
  rw [h j] at hj
  contradiction

private theorem equivalence_of_equal_kernels
    {F U V Z : Type*} [Field F]
    [AddCommGroup U] [Module F U] [AddCommGroup V] [Module F V]
    [AddCommGroup Z] [Module F Z]
    (f : U →ₗ[F] V) (g : U →ₗ[F] Z)
    (hf : Function.Surjective f) (hg : Function.Surjective g) (hk : f.ker=g.ker) :
    ∃ e : V ≃ₗ[F] Z, ∀ x, e (f x)=g x := by
  let e := (f.quotKerEquivOfSurjective hf).symm.trans
    ((Submodule.quotEquivOfEq _ _ hk).trans (g.quotKerEquivOfSurjective hg))
  refine ⟨e,?_⟩
  intro x
  change g.quotKerEquivOfSurjective hg
    (Submodule.quotEquivOfEq _ _ hk ((f.quotKerEquivOfSurjective hf).symm (f x)))=g x
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply,Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]

/-- Every nonzero surjective endpoint quotient with parabolic displacement
dimension at most seven is the literal four-space or six-space survivor,
with an equation retaining the original quotient map. -/
theorem exists_survivor_equivalence [Nontrivial W]
    (dual : Bool) (f : (Fin 45 → ZMod 2) →ₗ[ZMod 2] W)
    (hf : Function.Surjective f)
    (hinv : ∀ k : Fin 2, ∀ x, x ∈ f.ker → x ᵥ* generator dual k ∈ f.ker)
    (D : Submodule (ZMod 2) W) [FiniteDimensional (ZMod 2) D]
    (hdim : Module.finrank (ZMod 2) D ≤ 7)
    (hmem : ∀ k : Fin 4, ∀ x : Fin 45 → ZMod 2,
      f (x ᵥ* inducedCosetMatrix dual ⟨k.val+2,by omega⟩-x) ∈ D) :
    ∃ e : W ≃ₗ[ZMod 2] (Fin (if dual then 4 else 6) → ZMod 2),
      ∀ x, e (f (x ᵥ* changeMatrix dual))=survivorProjection dual x := by
  let fc := f.comp (changeMatrix dual).vecMulLinear
  have hfc : Function.Surjective fc := comp_row_map_surjective f hf
    (changeMatrix dual) (inverseChangeMatrix dual) (change_inverse dual).2
  obtain ⟨mask,hmask,hm⟩ := small_displacement_kernel dual f hinv D hdim hmem
  have hgood : mask.val=(if dual then 29 else 27) := by
    rcases hm with hm | hm
    · have he : mask=31 := Fin.ext hm
      have hk : fc.ker=⊤ := by rw [hmask,he,mask_full]
      have hz : ∀ w : W, w=0 := by
        intro w
        obtain ⟨x,rfl⟩ := hfc w
        exact LinearMap.mem_ker.mp (hk ▸ Submodule.mem_top)
      obtain ⟨w,hw⟩ := exists_ne (0 : W)
      exact False.elim (hw (hz w))
    · exact hm
  have hk : fc.ker=(survivorProjection dual).ker := by
    rw [hmask,survivorProjection_ker]
    exact congrArg maskSubspace (Fin.ext hgood)
  exact equivalence_of_equal_kernels fc (survivorProjection dual)
    hfc (survivorProjection_surjective dual) hk

end BinaryEndpointInduction
