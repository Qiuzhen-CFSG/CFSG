module

public import Theory.GroupTheory.Covering

/-!
# Comparing kernels of universal coverings

A commuting square of group isomorphisms restricts to an isomorphism of
kernels. Applying the comparison theorem for finite quasisimple universal
covers therefore transports an explicit Schur-multiplier calculation to any
chosen universal cover of an isomorphic base.

This is the choice-independence step in the multiplier calculations of
Aschbacher–Smith, *The Classification of Quasithin Groups*, I.1.1–I.1.4,
printed pp.407–408. Existence and the family-specific calculations remain
separate inputs; the comparison retains the group structure of the kernel.
-/

universe u v w z

namespace Theory.GroupTheory.Covering

/-- Isomorphisms forming a commuting square restrict to the kernels. -/
public def kerMulEquivOfSquare
    {L₁ : Type u} {L₂ : Type v} {K₁ : Type w} {K₂ : Type z}
    [Group L₁] [Group L₂] [Group K₁] [Group K₂]
    (f₁ : L₁ →* K₁) (f₂ : L₂ →* K₂) (e : L₁ ≃* L₂) (c : K₁ ≃* K₂)
    (h : ∀ x, f₂ (e x) = c (f₁ x)) : f₁.ker ≃* f₂.ker where
  toFun x := ⟨e x, by change f₂ (e x) = 1; rw [h, x.property, map_one]⟩
  invFun y := ⟨e.symm y, by
    apply c.injective
    rw [map_one, ← h, e.apply_symm_apply]
    exact y.property⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv y := Subtype.ext (e.apply_symm_apply y)
  map_mul' x y := Subtype.ext (e.map_mul x y)

variable {K₁ K₂ L₁ L₂ : Type u}
variable [Group K₁] [Finite K₁] [IsQuasisimple K₁]
variable [Group K₂] [Finite K₂] [IsQuasisimple K₂]
variable [Group L₁] [Finite L₁] [IsQuasisimple L₁]
variable [Group L₂] [Finite L₂] [IsQuasisimple L₂]
variable {f₁ : Covering L₁ K₁} {f₂ : Covering L₂ K₂}

/-- Chosen universal covers of isomorphic groups have isomorphic kernels. -/
public noncomputable def IsUniversal.kerMulEquiv
    (hf₁ : IsUniversal.{u, u, u} f₁) (hf₂ : IsUniversal.{u, u, u} f₂)
    (c : K₁ ≃* K₂) : f₁.toMonoidHom.ker ≃* f₂.toMonoidHom.ker := by
  let e := Classical.choose
    (existsUnique_mulEquiv_of_isUniversal (ofMulEquiv c) f₁ f₂ hf₁ hf₂)
  have he := (Classical.choose_spec
    (existsUnique_mulEquiv_of_isUniversal (ofMulEquiv c) f₁ f₂ hf₁ hf₂)).1
  exact kerMulEquivOfSquare f₁.toMonoidHom f₂.toMonoidHom e c
    (fun x => congrArg (fun q : Covering L₁ K₂ => q x) he)

/-- A multiplier calculation as a group isomorphism is independent of the
chosen universal covering and of the isomorphic model of the base group. -/
public theorem IsUniversal.schurMultiplier_nonempty_mulEquiv_iff
    (hf₁ : IsUniversal.{u, u, u} f₁) (hf₂ : IsUniversal.{u, u, u} f₂)
    (c : K₁ ≃* K₂) (A : Type v) [Group A] :
    Nonempty (schurMultiplier f₁ hf₁ ≃* A) ↔
      Nonempty (schurMultiplier f₂ hf₂ ≃* A) := by
  let e := hf₁.kerMulEquiv hf₂ c
  exact ⟨fun ⟨a⟩ => ⟨e.symm.trans a⟩, fun ⟨a⟩ => ⟨e.trans a⟩⟩

end Theory.GroupTheory.Covering
