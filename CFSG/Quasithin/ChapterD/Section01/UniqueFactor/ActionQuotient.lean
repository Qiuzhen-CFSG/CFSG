module
public import CFSG.Quasithin.ChapterD.Section01.UniqueFactor.Setup
public import Theory.Representation.BinaryOffender.CubicRatio.Equivariant
public import Theory.Representation.NormalElementaryQuotient
/-!
# Cubic bounds on the literal centralizer quotient

The conjugation image and any faithful centralizer quotient act on the
same original subgroup. Descend the quotient map through the conjugation
image, then use the subgroup-of equivalence to identify the underlying
binary modules. Faithfulness proves that the actor map is injective, so
an actual cubic actor and its dimension/rank bound transfer unchanged.

This is the action identification used in Aschbacher--Smith 3.1.6--8 and
3.2.5--6, printed pp.573--581.
-/

public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterD.UniqueFactor
variable {G Q : Type*} [Group G] [Finite G] [Group Q] [Finite Q]

theorem cubicRatio_quotient_le_nat_of_image
    (H V : Subgroup G) [IsElementaryAbelian 2 V]
    (hVH : V ≤ H) (hn : H ≤ normalizer (V : Set G))
    (q : H →* Q) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (V.subgroupOf H : Set H)) (n : ℕ) :
    letI : (V.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer hn
    letI : IsElementaryAbelian 2 (V.subgroupOf H) := IsElementaryAbelian.subgroupOf hVH
    cubicRatio (imageRepresentation H V hn) ≤ n →
      cubicRatio (Representation.NormalElementaryQuotient.representation
        (V.subgroupOf H) q hq hk) ≤ n := by
  let W := V.subgroupOf H
  let : W.Normal := normal_subgroupOf_of_le_normalizer hn
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hVH
  let f := actionHom H V hn
  let r := f.rangeRestrict
  have hr : Function.Surjective r := f.rangeRestrict_surjective
  have hker : r.ker ≤ q.ker := by
    rw [MonoidHom.ker_rangeRestrict, actionHom_ker, hk]
    intro g hg v hv
    exact Subtype.ext (hg v hv)
  let η := r.liftOfSurjective hr ⟨q,hker⟩
  have hη (g : H) : η (r g) = q g := r.liftOfRightInverse_comp_apply _ _ _ g
  let e := (subgroupOfEquivOfLe hVH).symm
  let E : Additive V ≃ₗ[ZMod 2] Additive W :=
    LinearEquiv.ofBijective (e.toMonoidHom.toAdditive.toZModLinearMap 2) e.bijective
  let ρ := imageRepresentation H V hn
  let σ := Representation.NormalElementaryQuotient.representation W q hq hk
  have he : ∀ a v, E (ρ a v) = σ (η a) (E v) := by
    intro a v
    obtain ⟨g,rfl⟩ := hr a
    rw [hη]
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    exact (congrArg H.subtype
      (Representation.NormalElementaryQuotient.representation_apply W q hq hk g (E v))).symm
  have hi : Function.Injective η := by
    intro a b hab
    apply imageRepresentation_injective H V hn
    apply LinearMap.ext
    intro v
    apply E.injective
    change E (ρ a v) = E (ρ b v)
    exact (he a v).trans ((congrArg (fun z => σ z (E v)) hab).trans (he b v).symm)
  exact cubicRatio_le_nat_of_equivariant ρ σ η hi E he n
end CFSG.Quasithin.ChapterD.UniqueFactor
