module
public import Theory.Representation.BinaryFifteenPoint.SingerRanks

/-!
# Cubic ranks retaining an arbitrary actual fifteen-point quotient map

Equal kernels identify the given quotient with one of the eight checked
coordinate rows. Intertwining retains its actual Singer endomorphism, so
both reciprocal cubic kernels have their certified dimensions. No row is
discarded and no composition-factor count is inferred.
-/
public noncomputable section
namespace BinaryFifteenPoint
open Matrix Polynomial

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

private theorem intertwine_aeval
    {V₁ V₂ : Type*} [AddCommGroup V₁] [AddCommGroup V₂]
    [Module (ZMod 2) V₁] [Module (ZMod 2) V₂]
    (a : Module.End (ZMod 2) V₁) (b : Module.End (ZMod 2) V₂)
    (f : V₁ →ₗ[ZMod 2] V₂) (hf : ∀ x, f (a x)=b (f x))
    (p : (ZMod 2)[X]) (x : V₁) : f (aeval a p x)=aeval b p (f x) := by
  have hpow : ∀ k x, f ((a^k) x)=(b^k) (f x) := by
    intro k x
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ',Module.End.mul_apply,hf,ih,pow_succ',Module.End.mul_apply]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add,LinearMap.add_apply,hp,hq]
  | monomial k c =>
    simp only [Polynomial.aeval_monomial,Module.End.mul_apply,Module.algebraMap_end_apply,
      map_smul,hpow]

private theorem kernel_finrank_eq_of_intertwining_equiv
    {V₁ V₂ : Type*} [AddCommGroup V₁] [AddCommGroup V₂]
    [Module (ZMod 2) V₁] [Module (ZMod 2) V₂]
    (a : Module.End (ZMod 2) V₁) (b : Module.End (ZMod 2) V₂)
    (e : V₁ ≃ₗ[ZMod 2] V₂) (he : ∀ x, e (a x)=b (e x))
    (p : (ZMod 2)[X]) :
    Module.finrank (ZMod 2) (LinearMap.ker (aeval a p))=
      Module.finrank (ZMod 2) (LinearMap.ker (aeval b p)) := by
  have hpoly (x : V₁) : e (aeval a p x)=aeval b p (e x) :=
    intertwine_aeval a b e.toLinearMap he p x
  have hk : (LinearMap.ker (aeval a p)).map e.toLinearMap=LinearMap.ker (aeval b p) := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      apply LinearMap.mem_ker.mpr
      change aeval b p (e x)=0
      rw [←hpoly,LinearMap.mem_ker.mp hx,map_zero]
    · intro hy
      refine ⟨e.symm y,?_,e.apply_symm_apply y⟩
      apply LinearMap.mem_ker.mpr
      apply e.injective
      rw [hpoly,e.apply_symm_apply,map_zero]
      exact LinearMap.mem_ker.mp hy
  rw [←hk,e.finrank_map_eq]

/-- A given onto quotient with its exact frozen kernel is identified with
that row, preserving every original vector and its Singer action. -/
theorem exists_singer_quotient_equivalence
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (r : Fin 8) (f : (Fin 15 → ZMod 2) →ₗ[ZMod 2] W)
    (hf : Function.Surjective f) (hk : f.ker=invariantSubspace r)
    (A : Module.End (ZMod 2) W)
    (hA : ∀ x, f (x ᵥ* singerMatrix)=A (f x)) :
    ∃ e : W ≃ₗ[ZMod 2] (Fin (quotientDimension r) → ZMod 2),
      (∀ x, e (f x)=quotientProjection r x) ∧
      ∀ w, e (A w)=e w ᵥ* singerQuotientMatrix r := by
  obtain ⟨e,he⟩ := equivalence_of_equal_kernels f (quotientProjection r) hf
    (quotientProjection_surjective r) (hk.trans (quotientProjection_ker r).symm)
  refine ⟨e,he,?_⟩
  intro w
  obtain ⟨x,rfl⟩ := hf w
  rw [←hA,he,he,quotientProjection_singer_intertwine]

/-- Both reciprocal cubic kernel ranks transfer to the same given quotient
and the same given Singer endomorphism, with no simplicity hypothesis. -/
theorem quotient_singer_cubic_kernel_finrank
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (r : Fin 8) (f : (Fin 15 → ZMod 2) →ₗ[ZMod 2] W)
    (hf : Function.Surjective f) (hk : f.ker=invariantSubspace r)
    (A : Module.End (ZMod 2) W)
    (hA : ∀ x, f (x ᵥ* singerMatrix)=A (f x)) (b : Bool) :
    Module.finrank (ZMod 2) (LinearMap.ker (aeval A (singerCubic b)))=
      singerCubicKernelDimension b r := by
  obtain ⟨e,_,he⟩ := exists_singer_quotient_equivalence r f hf hk A hA
  rw [kernel_finrank_eq_of_intertwining_equiv A (singerQuotientMatrix r).vecMulLinear e he]
  exact singerQuotient_cubic_kernel_finrank b r

/-- Invariance under the original generating pair supplies a row while
retaining the actual quotient map and both of its cubic kernel ranks. -/
theorem exists_quotient_singer_cubic_ranks
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (f : (Fin 15 → ZMod 2) →ₗ[ZMod 2] W) (hf : Function.Surjective f)
    (hinv : ∀ (k : Fin 2) x, x ∈ f.ker →
      x ᵥ* permutationActor ⟨k.val,by omega⟩ ∈ f.ker)
    (A : Module.End (ZMod 2) W)
    (hA : ∀ x, f (x ᵥ* singerMatrix)=A (f x)) :
    ∃ r : Fin 8, f.ker=invariantSubspace r ∧ ∀ b : Bool,
      Module.finrank (ZMod 2) (LinearMap.ker (aeval A (singerCubic b)))=
        singerCubicKernelDimension b r := by
  obtain ⟨r,hr⟩ := quotient_kernel f hinv
  exact ⟨r,hr,quotient_singer_cubic_kernel_finrank r f hf hr A hA⟩

end BinaryFifteenPoint
