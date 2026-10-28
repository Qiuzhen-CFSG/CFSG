module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Covered.ActionData
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction.CubicOrders.Transport
import all CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction.CubicOrders.Transport
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction.QuotientMarks
public import Theory.Representation.HexacodeAction.CubicLocalModel.Normalizer

/-!
# The covered Borel product has the action image of L₁

The permitted earlier factorization L₁ = XL₀ places L₁ in L. Its actual
conjugation action on L/O₂(L), transported through the given hexacode
isomorphism, is inner conjugation by its cover image. That image is the
point residual. The theta identity makes L₁ normal in BL₁, and the product
is two-perfect, so the concrete automorphism-normalizer calculation puts
its entire image in the image of L₁. The existing kernel reduction then
gives BL₁ = B_C L₁.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
13.8.20, printed p.954/PDF p.971; 13.2.2(3), printed p.877, and
13.7.3(9), printed p.936. The remaining B_C conclusions belong to the
source assembly, not to this action-image calculation.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Covered.ModelImage
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open LocalAction.CubicOrders
open Representation.Hexacode
universe u v
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {H K L V V₁ V₂ V₃ M G₁ : Subgroup G}
  [(Source.starImage H K).Normal] {n : ℕ} {unitary four : Bool}
  (d : SourceContext.{u,v} T H K L V V₁ V₂ V₃ M G₁ n unitary four)
  (a : LocalAction.NaturalSetup L (T : Subgroup G) V V₁ V₃)

/-- On L₁ the actual transported quotient action is inner conjugation.
Its kernel is retained; the cover group is not identified with its inner image. -/
theorem action_one
    (hfactor : one L (T : Subgroup G) V₁ = plus L (T : Subgroup G) V₁ ⊔ zero L)
    (l : one L (T : Subgroup G) V₁) :
    modelAction d a (inclusion le_sup_right l) =
      MulAut.conj (coverProjection a (inclusion
        (LocalAction.one_le_L_of_factorization _ _ _ a.normalizes_L hfactor) l)) := by
  apply MulEquiv.ext
  intro q
  obtain ⟨q, rfl⟩ := a.cover.surjective q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
  change a.cover (coreAction L _
    (a.cover.symm (a.cover (QuotientGroup.mk' (pCore 2 L) x)))) = _
  rw [a.cover.symm_apply_apply, coreAction_mk]
  let hL := LocalAction.one_le_L_of_factorization _ _ _ a.normalizes_L hfactor
  have hnorm := Subgroup.normalizerMonoidHom_apply_apply_coe L
    (inclusion d.product_normalizes_L (inclusion le_sup_right l)) x
  have hnormL : (L.normalizerMonoidHom
      (inclusion d.product_normalizes_L (inclusion le_sup_right l)) x : L) =
      (inclusion hL l) * x * (inclusion hL l)⁻¹ := by
    apply Subtype.ext
    exact hnorm
  have hnorm' := congrArg (QuotientGroup.mk' (pCore 2 L)) hnormL
  rw [hnorm']
  simp [coverProjection, MulAut.conj_apply, map_mul, map_inv]

/-- The image of the actual L₁ inclusion is the inner point-residual image. -/
theorem one_action_range
    (hfactor : one L (T : Subgroup G) V₁ = plus L (T : Subgroup G) V₁ ⊔ zero L) :
    ((modelAction d a).comp (inclusion le_sup_right)).range =
      (CubicLocalModel.pointResidual a.point).map
        (MulAut.conj : CubicLocalModel.H →* MulAut CubicLocalModel.H) := by
  rw [← coverImage_one a hfactor]
  have hL := LocalAction.one_le_L_of_factorization _ _ _ a.normalizes_L hfactor
  ext z
  constructor
  · rintro ⟨l, rfl⟩
    refine ⟨coverProjection a (inclusion hL l),
      (coverMap a (one L (T : Subgroup G) V₁) hL l).property, ?_⟩
    · exact (action_one d a hfactor l).symm
  · intro hz
    obtain ⟨w, hw, hzw⟩ := mem_map.mp hz
    obtain ⟨l, hl⟩ := coverMap_surjective a (one L (T : Subgroup G) V₁) hL ⟨w, hw⟩
    refine ⟨l, ?_⟩
    change modelAction d a (inclusion le_sup_right l) = z
    rw [action_one d a hfactor l]
    rw [← hzw]
    have hcov0 := congrArg Subtype.val hl
    change coverProjection a (inclusion hL l) = w at hcov0
    have hcov : coverProjection a (inclusion hL l) = w := hcov0
    rw [hcov]

/-- Every element of BL₁ has the same model action as some element of L₁. -/
theorem action_image
    (hfactor : one L (T : Subgroup G) V₁ = plus L (T : Subgroup G) V₁ ⊔ zero L) :
    ∀ g : (d.B ⊔ one L (T : Subgroup G) V₁ : Subgroup G),
    ∃ l : one L (T : Subgroup G) V₁,
      modelAction d a g = modelAction d a (inclusion le_sup_right l) := by
  let J := d.B ⊔ one L (T : Subgroup G) V₁
  let X := (one L (T : Subgroup G) V₁).subgroupOf J
  let f := modelAction d a
  let _ : X.Normal := (normal_subgroupOf_iff_le_normalizer le_sup_right).mpr
    (product_normalizes_one d)
  have he : X.map f = (CubicLocalModel.pointResidual a.point).map
      (MulAut.conj : CubicLocalModel.H →* MulAut CubicLocalModel.H) := by
    rw [show X = (inclusion (show one L (T : Subgroup G) V₁ ≤ J from le_sup_right)).range
      from (inclusion_range _).symm, ← MonoidHom.range_comp]
    simpa [f] using one_action_range d a hfactor
  have hn : f.range ≤ normalizer (X.map f : Set (MulAut CubicLocalModel.H)) := by
    rw [MonoidHom.range_eq_map, ← X.normalizer_eq_top]
    exact le_normalizer_map f
  have hp : IsPPerfect 2 f.range :=
    (product_isPPerfect d).of_surjective f.rangeRestrict f.rangeRestrict_surjective
  rw [he] at hn
  have hle := CubicLocalModel.twoPerfect_normalizer_pointResidual
    a.point a.point_dim f.range hp hn
  rw [← one_action_range d a hfactor] at hle
  intro g
  obtain ⟨l, hl⟩ := hle (show f g ∈ f.range from ⟨g, rfl⟩)
  exact ⟨l, hl.symm⟩

/-- The product's full action range, with the central conjugation kernel retained. -/
theorem action_range
    (hfactor : one L (T : Subgroup G) V₁ = plus L (T : Subgroup G) V₁ ⊔ zero L) :
    (modelAction d a).range =
    (CubicLocalModel.pointResidual a.point).map
      (MulAut.conj : CubicLocalModel.H →* MulAut CubicLocalModel.H) := by
  rw [← one_action_range d a hfactor]
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    obtain ⟨l, hl⟩ := action_image d a hfactor g
    exact ⟨l, hl.symm⟩
  · rintro _ ⟨l, rfl⟩
    exact ⟨inclusion le_sup_right l, rfl⟩

/-- The model calculation discharges the action-image premise of the source
product-factorization reduction. -/
theorem product_eq
    (a : LocalAction.NaturalSetup L (T : Subgroup G) V V₁ V₃)
    (hfactor : one L (T : Subgroup G) V₁ = plus L (T : Subgroup G) V₁ ⊔ zero L) :
    d.B ⊔ one L (T : Subgroup G) V₁ =
      centralizingResidual d.B (one L (T : Subgroup G) V₁) L ⊔
        one L (T : Subgroup G) V₁ :=
  product_eq_of_action_image d a (action_image d a hfactor)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Covered.ModelImage
