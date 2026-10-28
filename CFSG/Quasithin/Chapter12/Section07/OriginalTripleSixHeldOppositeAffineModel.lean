module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldOppositeFullActor
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldAffineModel
import all CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldScalarComplement
import Theory.GroupTheory.SplitExtensionGivenComplement

/-!
# The opposite normalizer has actual marked affine coordinates

The proved full action has exactly the original elementary kernel W.
The fixed-free normal scalar cubic supplies a complement by odd lifting
and Frattini. This derives the splitting, rather than inferring it from
an abstract quotient isomorphism, and preserves every original vector.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Atlas.Codes
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]

/-- The full original conjugation marking and its exact kernel construct
an affine equivalence, retaining both the full kernel and quotient maps. -/
theorem opposite_affine_of_full_action (W : Subgroup G) [IsElementaryAbelian 2 W]
    (hker : let I := normalizer (W : Set G)
      let ρ := BinaryInternalFixedSpaceCodimension.representation W I le_rfl
      (actionHom ρ).ker=W.subgroupOf I)
    (b : let I := normalizer (W : Set G)
      let ρ := BinaryInternalFixedSpaceCodimension.representation W I le_rfl
      ActionEquiv (imageRepresentation ρ) Hexacode.action) :
    let I := normalizer (W : Set G)
    let ρ := BinaryInternalFixedSpaceCodimension.representation W I le_rfl
    ∃ E : I≃*SextetAffineGroup,
      (∀ w : W, E (inclusion W.le_normalizer w)=
        SemidirectProduct.inl (Multiplicative.ofAdd (b.linearEquiv (Additive.ofMul w)))) ∧
      (∀ x : I, (E x).right=b.groupEquiv (actionHom ρ x)) := by
  let I := normalizer (W : Set G)
  let ρ := BinaryInternalFixedSpaceCodimension.representation W I le_rfl
  let f := b.groupEquiv.toMonoidHom.comp (actionHom ρ)
  have hf : Function.Surjective f := b.groupEquiv.surjective.comp ρ.asGroupHom.rangeRestrict_surjective
  have hk : f.ker=W.subgroupOf I := by
    rw [show f=b.groupEquiv.toMonoidHom.comp (actionHom ρ) from rfl,
      MonoidHom.ker_comp_of_injective _ _ b.groupEquiv.injective,hker]
  let c : W≃*Multiplicative hexacode := {
    toFun w := Multiplicative.ofAdd (b.linearEquiv (Additive.ofMul w))
    invFun v := (b.linearEquiv.symm v.toAdd).toMul
    left_inv w := b.linearEquiv.symm_apply_apply (Additive.ofMul w)
    right_inv v := b.linearEquiv.apply_symm_apply v.toAdd
    map_mul' v w := b.linearEquiv.map_add (Additive.ofMul v) (Additive.ofMul w) }
  let v : f.ker≃*W := (MulEquiv.subgroupCongr hk).trans
    (subgroupOfEquivOfLe W.le_normalizer)
  let w := v.trans c
  have hw (x : I) (u : f.ker) :
      w (MulAut.conjNormal x u)=hexAffineAction (f x) (w u) := by
    apply Multiplicative.toAdd.injective
    have he : Additive.ofMul (v (MulAut.conjNormal x u))=ρ x (Additive.ofMul (v u)) := by
      apply Additive.ofMul.injective
      apply Subtype.ext
      rfl
    change b.linearEquiv (Additive.ofMul (v (MulAut.conjNormal x u)))=
      Hexacode.action (f x) (b.linearEquiv (Additive.ofMul (v u)))
    rw [he]
    exact b.intertwines (actionHom ρ x) (Additive.ofMul (v u))
  have hp : IsPGroup 2 f.ker :=
    (IsElementaryAbelian.isPGroup 2 W).of_injective v.toMonoidHom v.injective
  have hn : (zpowers hexZ).Normal := by rw [←hexCoordinate_kernel]; infer_instance
  let := hn
  have hfix (x : I) (hx : f x=hexZ) (u : I) (hu : u∈f.ker)
      (hxu : x*u=u*x) : u=1 := by
    let q : f.ker := ⟨u,hu⟩
    have he : MulAut.conjNormal x q=q := by
      apply Subtype.ext
      change x*u*x⁻¹=u
      rw [hxu,mul_inv_cancel_right]
    have ha := hw x q
    rw [he,hx] at ha
    have hzero := (Hexacode.scalar_fixed_iff (w q).toAdd).mp
      (congrArg Multiplicative.toAdd ha.symm)
    have hq : q=1 := w.injective (hzero.trans (map_one w).symm)
    exact congrArg Subtype.val hq
  obtain ⟨C,_,_,hC⟩ := cubic_split f hf hp hexZ hexZ_order hfix
  obtain ⟨E,hEq,hEu,_,_⟩ := exists_marked_semidirect_equiv_of_given_complement
    f hf w hexAffineAction hw (normalizer (C : Set I)) hC
  refine ⟨E,?_,hEq⟩
  intro u
  let u' : f.ker := ⟨inclusion W.le_normalizer u,hk.symm ▸ u.property⟩
  exact hEu u'

end CFSG.Quasithin.Chapter12.Section07
