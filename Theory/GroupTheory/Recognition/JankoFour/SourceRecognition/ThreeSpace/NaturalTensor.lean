module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpace.PointNatural
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpace.Tensor

/-!
# The source radical as dual-natural tensor natural

The established equivalence R/Z(R) = Z* tensor W is composed with the SAME
natural coordinates on W constructed through RQ_z/Q_z. This gives a binary
linear tensor equivalence with the genuine F4 plane. The whole original
normalizer quotient and original Aut(Z) times S5 marking remain visible.
The transported full S5 action restricts on its marked alternating subgroup
to the natural SL2(4) matrices. Thus this proves the remaining natural-module
clause of AS91 (4.4), without discarding the odd part of the original actor.

Source: Aschbacher--Segev, *The uniqueness of groups of type J4*, Invent.
Math. 105 (1991), (4.4), printed pp.597--598, DOI 10.1007/BF01232280.
Later source point/line constructions and ambient recognition are separate
obligations; no such geometry is assumed here.
-/

@[expose] public section
noncomputable section
open Subgroup Representation
open scoped IsMulCommutative TensorProduct
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpaceData
variable {G : Type*} [Group G] [Finite G] {z : G}
variable {e : CubicAutomorphismQuotient (centralizer z ⧸ core z)}
  {X : Sylow 3 (LocalGeometry.CubicLift.subgroup e)}
variable (d : ThreeSpaceData z e X)
local instance : IsElementaryAbelian 2 d.space := d.elementary
attribute [local instance] R_normal_in_K R_normal_in_S_intrinsic R_normal_in_normalizer

/-- The full original S5 action in the proved natural coordinates. -/
def naturalMarkedAction (h : IsTypeJ4 z) :
    Equiv.Perm (Fin 5) →* (SL2FourNatural.V ≃ₗ[ZMod 2] SL2FourNatural.V) := by
  let := d.multiplicitySpace_elementary h
  let F := d.multiplicityNaturalEquiv h
  exact {
    toFun b := (F.symm.trans (binaryLinearAut (d.markedMultiplicityAction h b))).trans F
    map_one' := by
      apply LinearEquiv.ext
      intro v
      change F (Additive.ofMul (d.markedMultiplicityAction h 1 (F.symm v).toMul)) = v
      rw [map_one,MulAut.one_apply]
      exact F.apply_symm_apply v
    map_mul' a b := by
      apply LinearEquiv.ext
      intro v
      change F (Additive.ofMul (d.markedMultiplicityAction h (a*b) (F.symm v).toMul)) =
        F (Additive.ofMul (d.markedMultiplicityAction h a
          (F.symm (F (Additive.ofMul (d.markedMultiplicityAction h b (F.symm v).toMul)))).toMul))
      rw [map_mul,MulAut.mul_apply,F.symm_apply_apply]
      rfl }

/-- The coordinate change intertwines the entire original S5, including its odd elements. -/
theorem multiplicityNaturalEquiv_marked (h : IsTypeJ4 z) :
    letI := d.multiplicitySpace_elementary h
    ∀ (a : Equiv.Perm (Fin 5)) (w : Additive d.multiplicitySpace),
      d.multiplicityNaturalEquiv h (binaryLinearAut (d.markedMultiplicityAction h a) w) =
        d.naturalMarkedAction h a (d.multiplicityNaturalEquiv h w) := by
  let := d.multiplicitySpace_elementary h
  intro a w
  change _ = d.multiplicityNaturalEquiv h (binaryLinearAut (d.markedMultiplicityAction h a)
    ((d.multiplicityNaturalEquiv h).symm (d.multiplicityNaturalEquiv h w)))
  rw [LinearEquiv.symm_apply_apply]

/-- Its restriction to the marked alternating subgroup is the genuine natural matrix action. -/
theorem naturalMarkedAction_alternating (h : IsTypeJ4 z) (a : alternatingGroup (Fin 5)) :
    d.naturalMarkedAction h a.val = SL2FourNatural.action (d.markedNaturalActorEquiv h a) := by
  let := d.multiplicitySpace_elementary h
  apply LinearEquiv.ext
  intro v
  obtain ⟨w,rfl⟩ := (d.multiplicityNaturalEquiv h).surjective v
  rw [←d.multiplicityNaturalEquiv_marked]
  exact d.multiplicityNaturalEquiv_intertwines h a w

/-- Applying the same W coordinates to the tensor factor preserves the full marked action. -/
theorem exists_radical_natural_tensor_equiv (h : IsTypeJ4 z) :
    letI := d.R_center_quotient_elementary h
    ∃ F : Additive (d.R ⧸ center d.R) ≃ₗ[ZMod 2]
        Module.Dual (ZMod 2) (Additive d.space) ⊗[ZMod 2] SL2FourNatural.V,
      ∀ n : normalizer (d.space : Set G) ⧸ d.R.subgroupOf (normalizer (d.space : Set G)),
        ∀ v : Additive (d.R ⧸ center d.R),
      F (Additive.ofMul (d.radicalQuotientAction h n v.toMul)) =
        TensorProduct.congr
          (binaryLinearAut (d.markedNormalizerQuotientEquiv h n).1).symm.dualMap
          (d.naturalMarkedAction h (d.markedNormalizerQuotientEquiv h n).2) (F v) := by
  let := d.R_center_quotient_elementary h
  let := d.multiplicitySpace_elementary h
  obtain ⟨F,hF⟩ := d.exists_radical_normalizer_tensor_equiv h
  let C := TensorProduct.congr (LinearEquiv.refl (ZMod 2) (Module.Dual (ZMod 2) (Additive d.space)))
    (d.multiplicityNaturalEquiv h)
  refine ⟨F.trans C,?_⟩
  intro n v
  change C (F (Additive.ofMul (d.radicalQuotientAction h n v.toMul))) =
    TensorProduct.congr _ _ (C (F v))
  rw [hF]
  generalize F v = u
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul f w =>
      simp only [C,TensorProduct.congr_tmul,LinearEquiv.refl_apply]
      rw [d.multiplicityNaturalEquiv_marked]
  | add u v hu hv => simp only [map_add,hu,hv]

/-- The original Aut(Z) times A5 acts as dual-natural tensor natural in these same coordinates. -/
theorem exists_radical_alternating_natural_tensor_equiv (h : IsTypeJ4 z) :
    letI := d.R_center_quotient_elementary h
    ∃ F : Additive (d.R ⧸ center d.R) ≃ₗ[ZMod 2]
        Module.Dual (ZMod 2) (Additive d.space) ⊗[ZMod 2] SL2FourNatural.V,
      ∀ a : MulAut d.space, ∀ b : alternatingGroup (Fin 5),
        ∀ v : Additive (d.R ⧸ center d.R),
      F (Additive.ofMul (d.markedRadicalAction h (a,b.val) v.toMul)) =
        TensorProduct.congr (binaryLinearAut a).symm.dualMap
          (SL2FourNatural.action (d.markedNaturalActorEquiv h b)) (F v) := by
  let := d.R_center_quotient_elementary h
  obtain ⟨F,hF⟩ := d.exists_radical_natural_tensor_equiv h
  refine ⟨F,?_⟩
  intro a b v
  have he := hF ((d.markedNormalizerQuotientEquiv h).symm (a,b.val)) v
  rw [MulEquiv.apply_symm_apply,d.naturalMarkedAction_alternating] at he
  exact he

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpaceData
end
