module
public import Theory.Representation.OrthogonalFourMinusRankOne.FivePoint.CoverAction
public import Theory.Representation.NormalElementaryQuotient
public import Theory.Representation.BinaryPermutation.Faithful
/-!
# Extending the actual alternating-five conjugation action

The natural A5 cover determines an ambient S5 action by the concrete
four-dimensional normalizer theorem. Faithfulness of the natural permutation
module identifies its kernel with the original subgroup centralizer.
The direct conjugation representation keeps this transport at a small
instance boundary.

Source: Aschbacher–Smith C.1.23–26, printed pp.129–132.
-/
public section
open Subgroup BinaryPermutation Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne.PairedFive
variable {N : Type*} [Group N]

@[expose] noncomputable def conjugationAction (W : Subgroup N) [W.Normal] [IsElementaryAbelian 2 W] :
    Representation (ZMod 2) N (Additive W) where
  toFun g := (MulAut.conjNormal g : MulAut W).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    apply LinearMap.ext
    intro v
    apply Additive.toMul.injective
    apply Subtype.ext
    change 1 * (v.toMul : N) * 1⁻¹ = (v.toMul : N)
    simp only [one_mul,inv_one,mul_one]
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    apply Additive.toMul.injective
    apply Subtype.ext
    change (g*h) * (v.toMul:N) * (g*h)⁻¹ = g * (h*(v.toMul:N)*h⁻¹) * g⁻¹
    simp only [mul_inv_rev,mul_assoc]

theorem conjugationAction_apply (W : Subgroup N) [W.Normal] [IsElementaryAbelian 2 W]
    (g : N) (v : Additive W) : ((conjugationAction W g v).toMul : N) = g * (v.toMul : N) * g⁻¹ := by
  rfl

theorem quotient_action_apply (W : Subgroup N) [W.Normal] [IsElementaryAbelian 2 W]
    {D : Type*} [Group D] (p : N →* D) (hp : Function.Surjective p)
    (hk : p.ker = centralizer (W : Set N)) (g : N) (v : Additive W) :
    NormalElementaryQuotient.representation W p hp hk (p g) v = conjugationAction W g v := by
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [NormalElementaryQuotient.representation_apply,conjugationAction_apply]

theorem coreRepresentation_injective : Function.Injective (coreRepresentation (Fin 5)) := by
  intro g h he
  apply naturalRepresentation_injective (Fin 5) (by decide)
  apply LinearMap.ext
  intro v
  obtain ⟨w,rfl⟩ := (coreEquivNatural (Fin 5) (by decide)).surjective v
  rw [←coreEquivNatural_equivariant,←coreEquivNatural_equivariant,he]

theorem ambient_five_action
    (W : Subgroup N) [W.Normal] [IsElementaryAbelian 2 W]
    (L : Subgroup N) [L.Normal]
    (a : L →* alternatingGroup (Fin 5)) (ha : Function.Surjective a)
    (E : Additive W ≃ₗ[ZMod 2] core (Fin 5))
    (hE : ∀ (l : L) v, E (conjugationAction W l.val v) = coreRepresentation (Fin 5) (a l).val (E v)) :
    ∃ p : N →* Equiv.Perm (Fin 5), p.ker = centralizer (W : Set N) ∧
      L.map p = alternatingGroup (Fin 5) ∧
      ∀ g v, E (conjugationAction W g v) = coreRepresentation (Fin 5) (p g) (E v) := by
  let e := coreEquivNatural (Fin 5) (by decide)
  obtain ⟨p,hp,hl⟩ := OrthogonalFourMinus.FivePoint.exists_ambient_permutation_of_cover
    (conjugationAction W) L a ha (E.trans e) (by
      intro l v
      change e (E (conjugationAction W l.val v)) = _
      exact (congrArg e (hE l v)).trans (coreEquivNatural_equivariant (Fin 5) (by decide) (a l).val (E v)))
  have he (g : N) (v : Additive W) : E (conjugationAction W g v) = coreRepresentation (Fin 5) (p g) (E v) := by
    apply e.injective
    exact (hp g v).trans (coreEquivNatural_equivariant (Fin 5) (by decide) (p g) (E v)).symm
  refine ⟨p,?_,?_,he⟩
  · ext g
    constructor
    · intro hg w hw
      have h := he g (Additive.ofMul ⟨w,hw⟩)
      rw [show p g = 1 from hg,map_one,Module.End.one_apply] at h
      have hh := congrArg (fun v : Additive W => (v.toMul : N)) (E.injective h)
      rw [conjugationAction_apply] at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · intro hg
      apply coreRepresentation_injective
      apply LinearMap.ext
      intro v
      obtain ⟨w,rfl⟩ := E.surjective v
      have hfix : conjugationAction W g w = w := by
        apply Additive.toMul.injective
        apply Subtype.ext
        rw [conjugationAction_apply,←hg _ w.toMul.property,mul_inv_cancel_right]
      simpa only [map_one,Module.End.one_apply,hfix] using (he g w).symm
  · ext g
    constructor
    · rintro ⟨l,hl',rfl⟩
      exact (hl ⟨l,hl'⟩).symm ▸ (a ⟨l,hl'⟩).property
    · intro hg
      obtain ⟨l,hl'⟩ := ha ⟨g,hg⟩
      exact ⟨l,l.property,(hl l).trans (congrArg Subtype.val hl')⟩
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne.PairedFive
