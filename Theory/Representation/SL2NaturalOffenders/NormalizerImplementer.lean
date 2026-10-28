module
public import Theory.Representation.SL2NaturalOffenders.Semilinear
public import Mathlib.Algebra.Module.ZMod
public import Theory.SpecificGroups.PSL2.SemilinearCoverage

/-!
# Semilinear implementers for natural binary SL₂

The actual inner-field factorization of an automorphism constructs its
operator on the natural plane. The field coefficient and matrix action are
retained. In particular, an outer normalizer is not silently made linear
over the extension field.

Source application: Aschbacher–Smith 8.2.9, printed p.721,
refs/quasithin.pdf, on the homogeneous natural SL₂(4) chief section.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Representation.SL2NaturalOffenders
open Matrix
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

/-- Every automorphism of binary SL₂ is implemented on its natural module
by an actual base-field linear, field-semilinear equivalence. -/
theorem exists_semilinear_implementer (α : MulAut (SpecialLinearGroup (Fin 2) F)) :
    ∃ (τ : F ≃+* F) (s : (Fin 2 → F) ≃ₗ[ZMod 2] (Fin 2 → F)),
      (∀ g v, s (g.val *ᵥ v) = (α g).val *ᵥ s v) ∧
      (∀ c v, s (c • v) = τ c • s v) := by
  obtain ⟨g,τ,hα⟩ := Theory.PSL2.sl2_semilinear_coverage α
  let badd : (Fin 2 → F) ≃+ (Fin 2 → F) := {
    toFun v i := τ (v i)
    invFun v i := τ.symm (v i)
    left_inv v := by ext i; exact τ.symm_apply_apply _
    right_inv v := by ext i; exact τ.apply_symm_apply _
    map_add' v w := by ext i; exact map_add τ _ _ }
  let b : (Fin 2 → F) ≃ₗ[ZMod 2] (Fin 2 → F) :=
    LinearEquiv.ofBijective (badd.toAddMonoidHom.toZModLinearMap 2) badd.bijective
  let s := b.trans ((SpecialLinearGroup.toLin' g).restrictScalars (ZMod 2))
  have hb (d : SpecialLinearGroup (Fin 2) F) (v : Fin 2 → F) :
      b (d.val *ᵥ v) = (Theory.PSL2.sl2FieldAut τ d).val *ᵥ b v := by
    ext i
    change τ (∑ j, d.val i j * v j) = ∑ j, τ (d.val i j) * τ (v j)
    simp only [map_sum,map_mul]
  refine ⟨τ,s,?_,?_⟩
  · intro d v
    change g.val *ᵥ b (d.val *ᵥ v) = (α d).val *ᵥ (g.val *ᵥ b v)
    rw [hb,hα]
    change g.val *ᵥ ((Theory.PSL2.sl2FieldAut τ d).val *ᵥ b v) =
      (g * Theory.PSL2.sl2FieldAut τ d * g⁻¹).val *ᵥ (g.val *ᵥ b v)
    rw [Matrix.mulVec_mulVec,Matrix.mulVec_mulVec]
    change (g * Theory.PSL2.sl2FieldAut τ d).val *ᵥ b v =
      ((g * Theory.PSL2.sl2FieldAut τ d * g⁻¹) * g).val *ᵥ b v
    rw [inv_mul_cancel_right]
  · intro c v
    change g.val *ᵥ (fun i => τ (c * v i)) = τ c • (g.val *ᵥ b v)
    simp only [map_mul]
    exact Matrix.mulVec_smul g.val (τ c) (b v)
end Representation.SL2NaturalOffenders
