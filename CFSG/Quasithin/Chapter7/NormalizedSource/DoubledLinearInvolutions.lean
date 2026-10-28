module
public import Theory.Representation.IrreduciblePairNormalizer
public import Theory.Representation.SL3.NaturalNormalizerFixed
public import Theory.Representation.GeneralLinearNatural
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.Homogeneity

/-!
# Fixed vectors of involutions on the full linear-three pair

The actual inducing operator preserves or exchanges the two inequivalent
simple axes. In the preserving case each nonidentity natural block fixes
at most q² vectors. An identity block would make its actor automorphism
trivial and contradict the pair's trivial involution centralizer. In the
exchanging case a fixed vector is determined by its first coordinate.
Thus the whole pair has at most q⁴ fixed vectors. The full SL₃ scalar
center and the actual conjugation twist are retained.
Source: Aschbacher--Smith H.4 and Table7.2.1, pp.383--385,698.
-/

public noncomputable section
open Representation
namespace CFSG.Quasithin.Chapter7.NormalizedSource
open ChapterB.QuasisimpleSource

/-- A nonidentity involution in the actual normalizer fixes at most q⁴ vectors. -/
theorem doubledLinear_involution_fixed_card (F : BinaryField)
    (a α : MulAut (Matrix.SpecialLinearGroup (Fin 3) F.Carrier))
    (hne : ¬ Nonempty ((linearNatural F 3).Equiv
      ((linearNatural F 3).comp a.toMonoidHom)))
    (f : ((Fin 3 → F.Carrier) × (Fin 3 → F.Carrier)) ≃ₗ[ZMod 2]
      ((Fin 3 → F.Carrier) × (Fin 3 → F.Carrier)))
    (hfne : f ≠ LinearEquiv.refl _ _) (hsq : ∀ v, f (f v) = v)
    (hf : ∀ g v, f (((linearNatural F 3).prod
      ((linearNatural F 3).comp a.toMonoidHom)) g v) =
      ((linearNatural F 3).prod ((linearNatural F 3).comp a.toMonoidHom)) (α g) (f v)) :
    Nat.card {v // f v = v} ≤ Nat.card F.Carrier ^ 4 := by
  let W := Fin 3 → F.Carrier
  let σ := linearNatural F 3
  let τ := σ.comp a.toMonoidHom
  let : IsIrreducible σ := ExtensionConsequences.linearNatural_irreducible F (by decide)
  let : IsIrreducible τ := (irreducible_comp_surjective_iff
    a.toMonoidHom a.surjective σ).mpr inferInstance
  have hα : α ≠ MulEquiv.refl _ := by
    intro he
    apply hfne
    exact irreducible_pair_centralizing_involution σ τ hne f hsq
      (fun g v => by simpa only [he,MulEquiv.refl_apply] using hf g v)
  rcases irreducible_pair_normalizer_axes σ τ hne α f hf with hp | hx
  · have he (v : W × W) : f v = ((f (v.1,0)).1,(f (0,v.2)).2) := by
      have hv : v = (v.1,0) + (0,v.2) := by simp
      calc
        f v = f (v.1,0) + f (0,v.2) := by rw [←map_add,←hv]
        _ = _ := Prod.ext (by simpa using hp.2 v.2) (by simpa using hp.1 v.1)
    let b : W →ₗ[ZMod 2] W :=
      (LinearMap.fst _ _ _).comp (f.toLinearMap.comp (LinearMap.inl _ _ _))
    let c : W →ₗ[ZMod 2] W :=
      (LinearMap.snd _ _ _).comp (f.toLinearMap.comp (LinearMap.inr _ _ _))
    have hb : Function.Bijective b := ⟨by
      intro v w hvw
      exact congrArg Prod.fst (f.injective (Prod.ext hvw ((hp.1 v).trans (hp.1 w).symm))), by
      intro w
      refine ⟨(f.symm (w,0)).1,?_⟩
      exact (congrArg Prod.fst (he (f.symm (w,0)))).symm.trans
        (congrArg Prod.fst (f.apply_symm_apply (w,0)))⟩
    have hc : Function.Bijective c := ⟨by
      intro v w hvw
      exact congrArg Prod.snd (f.injective (Prod.ext ((hp.2 v).trans (hp.2 w).symm) hvw)), by
      intro w
      refine ⟨(f.symm (0,w)).2,?_⟩
      exact (congrArg Prod.snd (he (f.symm (0,w)))).symm.trans
        (congrArg Prod.snd (f.apply_symm_apply (0,w)))⟩
    let b' := (LinearEquiv.ofBijective b hb).toAddEquiv
    let c' := (LinearEquiv.ofBijective c hc).toAddEquiv
    have hbval (v : W) : b' v = (f (v,0)).1 := by
      exact LinearEquiv.ofBijective_apply b (hf := hb) v
    have hcval (v : W) : c' v = (f (0,v)).2 := by
      exact LinearEquiv.ofBijective_apply c (hf := hc) v
    have hbact (g) (v : W) : b' (specialLinearNatural 3 g v) =
        specialLinearNatural 3 (α g) (b' v) := by
      have hh := congrArg Prod.fst (hf g (v,0))
      change (f (specialLinearNatural 3 g v,specialLinearNatural 3 (a g) 0)).1 =
        specialLinearNatural 3 (α g) (f (v,0)).1 at hh
      rw [hbval,hbval]
      simpa only [map_zero] using hh
    have hcact (g) (v : W) : c' (specialLinearNatural 3 g v) =
        specialLinearNatural 3 ((a.symm.trans α).trans a g) (c' v) := by
      have hh := congrArg Prod.snd (hf (a.symm g) (0,v))
      change (f (specialLinearNatural 3 (a.symm g) 0,
        specialLinearNatural 3 (a (a.symm g)) v)).2 =
        specialLinearNatural 3 (a (α (a.symm g))) (f (0,v)).2 at hh
      rw [hcval,hcval]
      simpa only [map_zero,MulEquiv.apply_symm_apply,MulEquiv.trans_apply] using hh
    have hbne : b' ≠ AddEquiv.refl W := by
      intro hh
      apply hα
      apply MulEquiv.ext
      intro g
      apply specialLinearNatural_injective 3
      apply LinearMap.ext
      intro v
      simpa only [hh,AddEquiv.refl_apply,MulEquiv.refl_apply] using (hbact g v).symm
    have hcne : c' ≠ AddEquiv.refl W := by
      intro hh
      apply hα
      apply MulEquiv.ext
      intro g
      apply a.injective
      apply specialLinearNatural_injective 3
      apply LinearMap.ext
      intro v
      have hh' := hcact (a g) v
      simpa only [hh,AddEquiv.refl_apply,MulEquiv.trans_apply,MulEquiv.refl_apply,
        MulEquiv.symm_apply_apply] using hh'.symm
    let e : {v : W × W // f v = v} ≃
        ({v : W // b' v = v} × {v : W // c' v = v}) := {
      toFun := fun v =>
        (⟨v.val.1,(congrArg Prod.fst (he v)).symm.trans (congrArg Prod.fst v.property)⟩,
         ⟨v.val.2,(congrArg Prod.snd (he v)).symm.trans (congrArg Prod.snd v.property)⟩)
      invFun := fun v => ⟨(v.1.val,v.2.val),(he _).trans (Prod.ext v.1.property v.2.property)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    rw [Nat.card_congr e,Nat.card_prod]
    have hbnd := SL3NaturalFixed.fixed_card_le_of_intertwines b' hbne α hbact
    have hcnd := SL3NaturalFixed.fixed_card_le_of_intertwines c' hcne
      ((a.symm.trans α).trans a) hcact
    exact (Nat.mul_le_mul hbnd hcnd).trans_eq (by ring)
  · have he (v : W × W) : (f v).2 = (f (v.1,0)).2 := by
      have hv : v = (v.1,0) + (0,v.2) := by simp
      calc
        (f v).2 = (f (v.1,0)).2 + (f (0,v.2)).2 := by rw [←Prod.snd_add,←map_add,←hv]
        _ = _ := by rw [hx.2,add_zero]
    have hi : Function.Injective (fun v : {v : W × W // f v = v} => v.val.1) := by
      intro v w hvw
      change v.val.1 = w.val.1 at hvw
      apply Subtype.ext
      apply Prod.ext hvw
      calc
        v.val.2 = (f v.val).2 := (congrArg Prod.snd v.property).symm
        _ = (f (v.val.1,0)).2 := he _
        _ = (f (w.val.1,0)).2 := by rw [hvw]
        _ = (f w.val).2 := (he _).symm
        _ = w.val.2 := congrArg Prod.snd w.property
    apply (Nat.card_le_card_of_injective _ hi).trans
    change Nat.card (Fin 3 → F.Carrier) ≤ _
    rw [Nat.card_fun,Nat.card_fin]
    exact Nat.pow_le_pow_right Nat.card_pos (by decide)

end CFSG.Quasithin.Chapter7.NormalizedSource
