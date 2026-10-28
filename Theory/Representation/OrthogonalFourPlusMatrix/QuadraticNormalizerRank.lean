module

public import Theory.Representation.OrthogonalFourPlusMatrix.OuterElementaryRank
public import Theory.Representation.OrthogonalFourPlusMatrix.QuadraticActors

/-!
# Quadratic actors in the full determinant normalizer

An elementary actor of rank at least four lies in the original determinant
image. Quadraticity then bounds its order by four, giving a contradiction.
The conclusion applies to the full binary linear normalizer, including
operators exchanging the two simple factors.

Source: Aschbacher–Smith, the quadratic-actor alternatives in the proof of
14.7.32, printed p.1057; this bound is consumed on the literal critical
section in Chapter 14.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace ClassicalOrthogonal.FourPlusMatrix.Binary

local instance : Finite (Module.End (ZMod 2) V) :=
  Finite.of_injective DFunLike.coe DFunLike.coe_injective

/-- Every nontrivial elementary quadratic actor in the full binary determinant
normalizer has rank at most three. -/
theorem quadratic_normalizer_rank_le_three
    (A : Subgroup (linearNormalizer action))
    (hA : IsElementaryTwo A)
    (hq : IsQuadratic (normalizerRepresentation action) A) :
    rank A ≤ 3 := by
  let := hA.2
  by_contra hn
  have hc : 16 ≤ Nat.card A := by
    rw [hA.card_eq_two_pow_rank]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 4 ≤ rank A)
  have hin := large_elementary_le_actionImage A hc
  let f : A →* G :=
    actionImageEquiv.symm.toMonoidHom.comp
      ((linearNormalizer action).subtype.comp A.subtype
        |>.codRestrict _ (fun a => hin (mem_map_of_mem _ a.property)))
  have hf : Function.Injective f := by
    intro a b he
    have hh := congrArg actionImageEquiv he
    apply Subtype.ext
    apply Subtype.ext
    simp only [f,MonoidHom.coe_comp,Function.comp_apply,
      MulEquiv.coe_toMonoidHom,MulEquiv.apply_symm_apply] at hh
    exact congrArg (fun z : actionImage action => z.val) hh
  have he (a : A) : action (f a) = a.val.val.val := by
    have hh := MonoidHom.apply_ofInjective_symm
      action_asGroupHom_injective
      (⟨a.val.val,hin (mem_map_of_mem _ a.property)⟩ :
        actionImage action)
    exact congrArg Units.val hh
  let : IsElementaryAbelian 2 f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hq' : IsQuadratic action f.range := by
    rintro _ ⟨a,rfl⟩ _ ⟨b,rfl⟩ v
    rw [he,he]
    exact hq a a.property b b.property v
  have hsmall := ClassicalOrthogonal.FourPlusMatrix.QuadraticActors.card_le_four
    f.range inferInstance hq'
  rw [←Nat.card_congr (MonoidHom.ofInjective hf).toEquiv] at hsmall
  omega

end ClassicalOrthogonal.FourPlusMatrix.Binary
