module
public import Theory.Representation.FirstCohomology
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.Algebra.Group.Equiv.TypeTags

/-!
# Automorphisms fixing the normal factor of a faithful split extension

For a faithful action on an abelian group, an automorphism fixing the normal
factor pointwise also fixes the quotient: compare its conjugation on that
factor. Its displacement on the chosen complement is a crossed homomorphism.
Conversely, adding any crossed homomorphism to the first coordinate defines
an automorphism. These constructions identify the pointwise automorphism
kernel with the additive group of cocycles.

Source: Aschbacher, *Finite Group Theory* (1986), §17; used in
Aschbacher–Smith 14.3.19(10) for the natural split A₆ block.
-/

namespace Representation.OneCohomology
open SemidirectProduct
variable {k G W : Type*} [CommRing k] [Group G] [AddCommGroup W] [Module k W]
variable (ρ : Representation k G W) (φ : G →* MulAut (Multiplicative W))
variable (hφ : ∀ g v, (φ g v).toAdd = ρ g v.toAdd)

private theorem cocycle_one (f : cocycles ρ) : f.val 1 = 0 := by
  have h := f.property 1 1
  simpa using h.symm

@[expose] public def splitCocycleAut (f : cocycles ρ) : MulAut (Multiplicative W ⋊[φ] G) where
  toFun x := ⟨Multiplicative.ofAdd (x.left.toAdd + f.val x.right),x.right⟩
  invFun x := ⟨Multiplicative.ofAdd (x.left.toAdd - f.val x.right),x.right⟩
  left_inv x := by apply SemidirectProduct.ext; exact congrArg Multiplicative.ofAdd (add_sub_cancel_right _ _); rfl
  right_inv x := by apply SemidirectProduct.ext; exact congrArg Multiplicative.ofAdd (sub_add_cancel _ _); rfl
  map_mul' x y := by
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      change (x.left.toAdd + (φ x.right y.left).toAdd) + f.val (x.right*y.right) =
        (x.left.toAdd + f.val x.right) + (φ x.right (Multiplicative.ofAdd (y.left.toAdd+f.val y.right))).toAdd
      rw [hφ,hφ,f.property]
      change (x.left.toAdd + ρ x.right y.left.toAdd) + (ρ x.right (f.val y.right) + f.val x.right) =
        (x.left.toAdd + f.val x.right) + ρ x.right (y.left.toAdd + f.val y.right)
      rw [map_add]
      abel
    · rfl

@[expose] public def splitPointwiseKernel : Subgroup (MulAut (Multiplicative W ⋊[φ] G)) where
  carrier := {a | ∀ w : Multiplicative W, a (inl w) = inl w}
  one_mem' _ := rfl
  mul_mem' {a b} ha hb w := by
    change a (b (inl w)) = inl w
    rw [hb,ha]
  inv_mem' {a} ha w := by
    apply a.injective
    change a (a.symm (inl w)) = a (inl w)
    rw [MulEquiv.apply_symm_apply]
    exact (ha w).symm

@[expose] public def splitCocycleHom : Multiplicative (cocycles ρ) →* splitPointwiseKernel φ where
  toFun f := ⟨splitCocycleAut ρ φ hφ f.toAdd,by
    intro w
    apply SemidirectProduct.ext
    · change Multiplicative.ofAdd (w.toAdd + f.toAdd.val 1) = w
      rw [cocycle_one,add_zero]
      rfl
    · rfl⟩
  map_one' := by apply Subtype.ext; apply MulEquiv.ext; intro x; apply SemidirectProduct.ext; exact congrArg Multiplicative.ofAdd (add_zero _); rfl
  map_mul' f g := by
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    apply SemidirectProduct.ext
    · change Multiplicative.ofAdd (x.left.toAdd+(f.toAdd.val x.right+g.toAdd.val x.right)) =
        Multiplicative.ofAdd ((x.left.toAdd+g.toAdd.val x.right)+f.toAdd.val x.right)
      congr 1
      abel
    · rfl

public theorem splitCocycleHom_injective : Function.Injective (splitCocycleHom ρ φ hφ) := by
  intro f g h
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  funext a
  have he := congrArg (fun b : splitPointwiseKernel φ => (b.val (inr a)).left.toAdd) h
  change 0+f.toAdd.val a=0+g.toAdd.val a at he
  simpa only [zero_add] using he

public theorem split_conjugate_inl (x : Multiplicative W ⋊[φ] G) (w : Multiplicative W) :
    x * inl w * x⁻¹ = inl (φ x.right w) := by
  apply SemidirectProduct.ext
  · simp only [mul_left,left_inl,right_inl,mul_right,mul_one,inv_left]
    have hi : φ x.right (φ x.right⁻¹ x.left⁻¹) = x.left⁻¹ := by
      rw [← MulAut.mul_apply,← map_mul,mul_inv_cancel,map_one]
      rfl
    rw [hi]
    rw [mul_right_comm,mul_inv_cancel,one_mul]
  · simp

public theorem splitPointwiseKernel_right (faithful : Function.Injective φ)
    (a : splitPointwiseKernel φ) (x : Multiplicative W ⋊[φ] G) : (a.val x).right=x.right := by
  apply faithful
  apply MulEquiv.ext
  intro w
  apply inl_injective (φ := φ)
  rw [← split_conjugate_inl,← a.property w,← map_inv,← map_mul,← map_mul,
    split_conjugate_inl,a.property]

public theorem splitCocycleHom_surjective (faithful : Function.Injective φ) :
    Function.Surjective (splitCocycleHom ρ φ hφ) := by
  intro a
  let f : cocycles ρ := ⟨fun g => (a.val (inr g)).left.toAdd,by
    intro g h
    have he := congrArg (fun x : Multiplicative W ⋊[φ] G => x.left.toAdd)
      (map_mul a.val (inr g) (inr h))
    rw [← map_mul (inr : G →* Multiplicative W ⋊[φ] G)] at he
    change (a.val (inr (g*h))).left.toAdd =
      (a.val (inr g)).left.toAdd + (φ (a.val (inr g)).right (a.val (inr h)).left).toAdd at he
    rw [splitPointwiseKernel_right φ faithful a,hφ] at he
    exact he.trans (add_comm _ _)⟩
  refine ⟨Multiplicative.ofAdd f,?_⟩
  apply Subtype.ext
  apply MulEquiv.ext
  intro x
  have he : a.val x = inl x.left * a.val (inr x.right) := by
    calc
      a.val x = a.val (inl x.left * inr x.right) :=
        congrArg a.val (inl_left_mul_inr_right x).symm
      _ = _ := by rw [map_mul,a.property]
  apply SemidirectProduct.ext
  · rw [he]
    change Multiplicative.ofAdd (x.left.toAdd+f.val x.right) = x.left * φ 1 (a.val (inr x.right)).left
    rw [map_one]
    rfl
  · exact (splitPointwiseKernel_right φ faithful a x).symm

public noncomputable def splitCocycleEquiv (faithful : Function.Injective φ) :
    Multiplicative (cocycles ρ) ≃* splitPointwiseKernel φ :=
  MulEquiv.ofBijective (splitCocycleHom ρ φ hφ)
    ⟨splitCocycleHom_injective ρ φ hφ,splitCocycleHom_surjective ρ φ hφ faithful⟩
public theorem splitCocycleEquiv_apply (faithful : Function.Injective φ)
    (f : Multiplicative (cocycles ρ)) :
    (splitCocycleEquiv ρ φ hφ faithful f).val = splitCocycleAut ρ φ hφ f.toAdd := by rfl
end Representation.OneCohomology
