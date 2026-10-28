module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Ordinary.Action
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.OrdinaryNormalizer
public import Theory.SpecificGroups.AlternatingSix.OuterSolvable

/-!
# The actual ordinary Borel action image

Two-perfectness kills the image in Out(A₆), whose order is four. Thus
the conjugation action of BL₁ lifts to its natural six-letter inner action.
On L₁ this is exactly the prescribed natural permutation homomorphism.
The theta identity makes that point residual invariant. Its six-letter
normalizer has no further two-perfect subgroup, so the whole product
has the same action image as L₁.

Source: Aschbacher–Smith 13.7.3(9), p.936, and 13.8.20, printed p.954/PDF p.971.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Ordinary.ModelImage
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open AlternatingSix.ShadowLocal
open BinaryPermutation Representation.BinaryOffender
universe u v
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {H K L V V₁ V₂ V₃ M G₁ : Subgroup G}
  [(Source.starImage H K).Normal] {n : ℕ} {unitary four : Bool}
  (d : SourceContext.{u,v} T H K L V V₁ V₂ V₃ M G₁ n unitary four)
  (a : NaturalSetup L (T : Subgroup G) V V₁)

/-- The full source action is inner, because its domain is two-perfect. -/
theorem action_range_le_inner : (Action.modelAction d a).range ≤ AlternatingSix.ShadowLocal.inner := by
  let q := QuotientGroup.mk' AlternatingSix.ShadowLocal.inner
  have htwo : IsPGroup 2 (AutA6 ⧸ AlternatingSix.ShadowLocal.inner) := IsPGroup.of_card (n := 2) outer_card
  have he := (TwoKernels.product_isPPerfect d).hom_eq_one_of_isPGroup htwo
    (q.comp (Action.modelAction d a))
  rintro _ ⟨g, rfl⟩
  apply (QuotientGroup.eq_one_iff _).mp
  exact DFunLike.congr_fun he g

private noncomputable def productPermutation :
    (d.B ⊔ one L (T : Subgroup G) V₁ : Subgroup G) →* Equiv.Perm (Fin 6) :=
  (alternatingGroup (Fin 6)).subtype.comp
    (innerEquiv.symm.toMonoidHom.comp ((Action.modelAction d a).codRestrict AlternatingSix.ShadowLocal.inner
      (fun g => action_range_le_inner d a ⟨g, rfl⟩)))

private theorem productPermutation_action (g : (d.B ⊔ one L (T : Subgroup G) V₁ : Subgroup G)) :
    permutationAction (productPermutation d a g) = Action.modelAction d a g := by
  change permutationAction ((innerEquiv.symm
    ⟨Action.modelAction d a g, action_range_le_inner d a ⟨g, rfl⟩⟩ : A6) : Equiv.Perm (Fin 6)) = _
  rw [permutationAction_coe]
  exact congrArg Subtype.val (innerEquiv.apply_symm_apply _)

/-- The quotient marking and the permutation marking give the same action of L₁. -/
theorem action_one (l : one L (T : Subgroup G) V₁) :
    Action.modelAction d a (inclusion le_sup_right l) =
      permutationAction (NaturalImage.onePermutation a l) := by
  apply MulEquiv.ext
  intro q
  obtain ⟨q, rfl⟩ := a.model.surjective q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
  change a.model (coreAction L _ (a.model.symm (a.model (QuotientGroup.mk' (pCore 2 L) x)))) = _
  rw [a.model.symm_apply_apply, coreAction_mk]
  apply Subtype.ext
  rw [← a.model_compatible]
  let y : (L ⊔ (T : Subgroup G) : Subgroup G) :=
    inclusion ((one_le _ _ _).trans inf_le_left) l
  change a.permutation (y * inclusion le_sup_left x * y⁻¹) = _
  rw [map_mul, map_mul, map_inv, a.model_compatible]
  rfl

private theorem productPermutation_one :
    (productPermutation d a).comp (inclusion le_sup_right) = NaturalImage.onePermutation a := by
  apply MonoidHom.ext
  intro l
  apply permutationAction_injective
  exact (productPermutation_action d a _).trans (action_one d a l)

/-- The image is the residual of the actual point stabilizer, including its four-core. -/
theorem onePermutation_range :
    (NaturalImage.onePermutation a).range =
      (pResidual 2 (a.permutation.range ⊓
        subspaceStabilizer (naturalRepresentation (Fin 6)) a.point : Subgroup (Equiv.Perm (Fin 6)))).map
          (a.permutation.range ⊓ subspaceStabilizer (naturalRepresentation (Fin 6)) a.point).subtype := by
  let M := parabolic L (T : Subgroup G) V₁
  let f : M →* Equiv.Perm (Fin 6) := a.permutation.comp (inclusion inf_le_left)
  have he : (NaturalImage.onePermutation a).range = (pResidual 2 M).map f := by
    ext g
    constructor
    · rintro ⟨⟨x, y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y.val, y, hy, rfl⟩, rfl⟩
  have hm : (pResidual 2 M).map f = (pResidual 2 f.range).map f.range.subtype := by
    calc
      _ = ((pResidual 2 M).map f.rangeRestrict).map f.range.subtype := by rw [map_map]; rfl
      _ = _ := by rw [map_pResidual_of_surjective 2 f.rangeRestrict f.rangeRestrict_surjective]
  rw [he, hm]
  change _ = _
  rw [show f.range = a.permutation.range ⊓ subspaceStabilizer (naturalRepresentation (Fin 6)) a.point
    from a.line_normalizer_image]

/-- The concrete ordinary action image is covered by L₁. -/
theorem action_image : ∀ g : (d.B ⊔ one L (T : Subgroup G) V₁ : Subgroup G),
    ∃ l : one L (T : Subgroup G) V₁,
      Action.modelAction d a g = Action.modelAction d a (inclusion le_sup_right l) := by
  let J := d.B ⊔ one L (T : Subgroup G) V₁
  let X := (one L (T : Subgroup G) V₁).subgroupOf J
  let f := productPermutation d a
  let _ : X.Normal := (normal_subgroupOf_iff_le_normalizer le_sup_right).mpr
    (TwoKernels.product_normalizes_one d)
  have he : X.map f = (NaturalImage.onePermutation a).range := by
    rw [show X = (inclusion (show one L (T : Subgroup G) V₁ ≤ J from le_sup_right)).range
      from (inclusion_range _).symm, ← MonoidHom.range_comp]
    exact congrArg MonoidHom.range (productPermutation_one d a)
  have hn : f.range ≤ normalizer ((NaturalImage.onePermutation a).range : Set (Equiv.Perm (Fin 6))) := by
    rw [← he, MonoidHom.range_eq_map, ← X.normalizer_eq_top]
    exact le_normalizer_map f
  have hperf : IsPPerfect 2 f.range :=
    (TwoKernels.product_isPPerfect d).of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hr := Theory.SpecificGroups.SymmetricSix.BinaryFlags.OrdinaryNormalizer.le_point_residual_of_isPPerfect
    a.permutation.range a.alternating_le_range a.point a.point_dim f.range hperf
  dsimp only at hr
  rw [← onePermutation_range a] at hr
  have hle := hr hn
  intro g
  obtain ⟨l, hl⟩ := hle (show f g ∈ f.range from ⟨g, rfl⟩)
  refine ⟨l, ?_⟩
  rw [← productPermutation_action d a, action_one d a]
  exact congrArg permutationAction hl.symm

/-- The full action image is the prescribed inner natural A₄ image. -/
theorem action_range : (Action.modelAction d a).range =
    (NaturalImage.onePermutation a).range.map permutationAction := by
  ext z
  constructor
  · rintro ⟨g, rfl⟩
    obtain ⟨l, hl⟩ := action_image d a g
    exact ⟨NaturalImage.onePermutation a l, ⟨l, rfl⟩,
      (action_one d a l).symm.trans hl.symm⟩
  · rintro ⟨p, ⟨l, rfl⟩, rfl⟩
    exact ⟨inclusion le_sup_right l, action_one d a l⟩

/-- The actual action image has order twelve, retaining its Klein four kernel. -/
theorem action_range_card : Nat.card (Action.modelAction d a).range = 12 := by
  rw [action_range]
  let e := (NaturalImage.onePermutation a).range.equivMapOfInjective
    permutationAction permutationAction_injective
  exact (Nat.card_congr e.toEquiv).symm.trans (NaturalImage.onePermutation_range_card a)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Ordinary.ModelImage
