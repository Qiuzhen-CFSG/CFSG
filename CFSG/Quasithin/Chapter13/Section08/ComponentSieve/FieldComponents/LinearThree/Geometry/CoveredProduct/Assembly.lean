module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.Centralizer
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.MarkedProduct

/-!
# Assembly of the covered-A₆ product geometry

The natural covered action and the earlier factorization, normalizer and
Fitting results first construct the residual placement and corrected inverter.
The two-reduced centralizer is then identified with S₃, marking the actual
cubic subgroup and inverter. Its product with the component gives one
point-oriented equivalence for H*, all seven subgroup marks and four
intrinsic two-core marks. In particular the two-core of L₀* survives.

The output retains the original source component action and seed. The
critical containment and both seed commutator identities therefore use the
same group equivalence as the later tensor argument. The independent input
K* ≃ L₃(2) and the genuine earlier source clauses are explicit; the product
and all its marks are constructed here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.21(1), covered-A₆ paragraph, printed p.957; Notation 13.2.1 and
13.2.2(3),(9) supply the source residuals and normalizer input.
-/

@[expose] public section
open Subgroup Matrix.PSL3Two
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct
open ResidualPlacement
variable {G : Type*} [Group G]

/-- The derived covered geometry and one compatible product identification.
All marks refer to this single equivalence, including its point orientation. -/
structure SourceProductGeometry (H K L T V₁ V₃ : Subgroup G)
    (eK : Source.starImage H K ≃* BinaryLinearThree.Group) where
  component : SourceComponentGeometry H K L T V₁ V₃ eK
  plus_le : plus L T V₁ ≤ H
  plus_le_one : plus L T V₁ ≤ one L T V₁
  parabolic_le : one L T V₁ ⊔ T ≤ H
  parabolic_seed_normalizes : one L T V₁ ⊔ T ≤ normalizer (V₃ : Set G)
  equiv : Source.Hstar H ≃* BinaryLinearThree.Group × Equiv.Perm (Fin 3)
  component_apply : ∀ k : Source.starImage H K,
    equiv k.val = (MarkedProduct.pointComponentEquiv H K L T eK component.placement k, 1)
  component_image : (Source.starImage H K).map equiv.toMonoidHom =
    (⊤ : Subgroup BinaryLinearThree.Group).prod ⊥
  zero_image : (Source.starImage H (zero L)).map equiv.toMonoidHom =
    (MarkedAutomorphisms.residual pointParabolicSL).prod ⊥
  plus_image : (Source.starImage H (plus L T V₁)).map equiv.toMonoidHom =
    (⊥ : Subgroup BinaryLinearThree.Group).prod (alternatingGroup (Fin 3))
  one_image : (Source.starImage H (one L T V₁)).map equiv.toMonoidHom =
    (MarkedAutomorphisms.residual pointParabolicSL).prod (alternatingGroup (Fin 3))
  sylow_image : (Source.starImage H T).map equiv.toMonoidHom =
    borelSL.prod Matrix.PSL3Two.MarkedProduct.R
  zeroT_image : (Source.starImage H (zero L ⊔ T)).map equiv.toMonoidHom =
    pointParabolicSL.prod Matrix.PSL3Two.MarkedProduct.R
  oneT_image : (Source.starImage H (one L T V₁ ⊔ T)).map equiv.toMonoidHom =
    pointParabolicSL.prod (⊤ : Subgroup (Equiv.Perm (Fin 3)))
  inverter_image : equiv (QuotientGroup.mk' (pCore 2 H)
      ⟨component.inverter.val,component.inverter_mem⟩) = (1,Equiv.swap (1 : Fin 3) 2)
  zero_core_image : (Source.starImage H ((zero L).pCoreIn 2)).map equiv.toMonoidHom =
    MarkedAutomorphisms.pointV.prod ⊥
  sylow_core_image : (Source.starImage H (T.pCoreIn 2)).map equiv.toMonoidHom =
    borelSL.prod Matrix.PSL3Two.MarkedProduct.R
  zeroT_core_image : (Source.starImage H ((zero L ⊔ T).pCoreIn 2)).map equiv.toMonoidHom =
    MarkedAutomorphisms.pointV.prod Matrix.PSL3Two.MarkedProduct.R
  oneT_core_image : (Source.starImage H ((one L T V₁ ⊔ T).pCoreIn 2)).map equiv.toMonoidHom =
    MarkedAutomorphisms.pointV.prod ⊥

/-- Assemble the covered-A₆ group geometry from the genuine earlier source
inputs and the independently supplied K* ≃ L₃(2). The normalizer equality is
13.2.2(9) in the standing setup, the factorization is 13.2.2(3), and the
Fitting alternative is 13.8.14. No product, residual placement, inner action,
inverter, centralizer identification or subgroup mark is assumed. -/
theorem source_product_geometry [Finite G] (H K L T V V₁ V₃ M : Subgroup G)
    (d : LocalAction.NaturalSetup L T V V₁ V₃)
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    [(K.subgroupOf H).Normal]
    (hgen : H = K ⊔ (one L T V₁ ⊔ T))
    (hnot : ¬ one L T V₁ ≤ K)
    (hKM : ¬ K ≤ M) (hNM : normalizer (zero L : Set G) = M)
    (S : Sylow 2 H) (hS : (S : Subgroup H).map H.subtype = T)
    (eK : Source.starImage H K ≃* BinaryLinearThree.Group)
    (hfit : fittingPreimageResidual H = ⊥ ∨
      (Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
        fittingPreimageResidual H = one L T V₁) ∨
      fittingPreimageResidual H = plus L T V₁) :
    Nonempty (SourceProductGeometry H K L T V₁ V₃ eK) := by
  obtain ⟨geo⟩ := source_component_geometry H K L T V V₁ V₃ M d hfactor
    hgen hnot hKM hNM.le S hS eK hfit
  obtain ⟨hs,eC,hC,ht⟩ := source_centralizer_equiv H K L T V₁ V₃ hgen hfactor S hS eK geo
  have ht' : eC ⟨MarkedProduct.inverterStar H K L T V₁ V₃ eK geo,
      MarkedProduct.inverterStar_mem H K L T V₁ V₃ eK geo⟩ = Equiv.swap (1 : Fin 3) 2 := ht
  have hKH : K ≤ H := by rw [hgen]; exact le_sup_left
  have hDH : one L T V₁ ≤ H := by rw [hgen]; exact le_sup_left.trans le_sup_right
  have hTH : T ≤ H := by rw [hgen]; exact le_sup_right.trans le_sup_right
  have hXH : plus L T V₁ ≤ H := (plus_le_one L T V₁ d.line_stable).trans hDH
  have hPN : one L T V₁ ⊔ T ≤ normalizer (V₃ : Set G) := by
    rw [hfactor]
    exact sup_le (sup_le geo.plus_seed_normalizes
      ((d.zero_centralizes.trans (centralizer_le d.seed_le)).trans (Subgroup.centralizer_le_normalizer _)))
      d.seed_stable
  obtain ⟨hz,hsyl,hzt,hot⟩ :=
    MarkedProduct.core_images H K L T V₁ V₃ eK geo eC hgen hfactor S hS hC ht'
  refine ⟨{
    component := geo
    plus_le := hXH
    plus_le_one := plus_le_one L T V₁ d.line_stable
    parabolic_le := sup_le hDH hTH
    parabolic_seed_normalizes := hPN
    equiv := MarkedProduct.equiv H K L T V₁ V₃ eK geo eC
    component_apply := ?_
    component_image := MarkedProduct.component_image H K L T V₁ V₃ eK geo eC
    zero_image := MarkedProduct.zero_image H K L T V₁ V₃ eK geo eC
    plus_image := MarkedProduct.plus_image H K L T V₁ V₃ eK geo eC hC
    one_image := MarkedProduct.one_image H K L T V₁ V₃ eK geo eC hKH hDH hfactor hC
    sylow_image := MarkedProduct.sylow_image H K L T V₁ V₃ eK geo eC hTH S hS ht'
    zeroT_image := MarkedProduct.zeroT_image H K L T V₁ V₃ eK geo eC hKH hTH S hS ht'
    oneT_image := MarkedProduct.oneT_image H K L T V₁ V₃ eK geo eC hKH hDH hTH hfactor S hS hC ht'
    inverter_image := MarkedProduct.inverter_image H K L T V₁ V₃ eK geo eC ht'
    zero_core_image := hz
    sylow_core_image := hsyl
    zeroT_core_image := hzt
    oneT_core_image := hot }⟩
  exact productEquiv_component H K (MarkedProduct.pointComponentEquiv H K L T eK geo.placement)
    eC geo.inner_action

namespace SourceProductGeometry
variable {H K L T V₁ V₃ : Subgroup G}
    {eK : Source.starImage H K ≃* BinaryLinearThree.Group}
    (geo : SourceProductGeometry H K L T V₁ V₃ eK)

/-- Transport the earlier critical containment through the constructed product.
The intrinsic core is the full marked four-group. -/
theorem critical_image_le [Finite G] (Vα : Subgroup G)
    (hα : Source.starImage H Vα ≤ (Source.starImage H (one L T V₁ ⊔ T)).pCoreIn 2) :
    (Source.starImage H Vα).map geo.equiv.toMonoidHom ≤ MarkedAutomorphisms.pointV.prod ⊥ := by
  have hm := map_mono (f := geo.equiv.toMonoidHom) hα
  rw [map_pCoreIn_of_injective 2 _ _ geo.equiv.injective, geo.oneT_image,
    Matrix.PSL3Two.MarkedProduct.point_full_product_core] at hm
  exact hm

/-- The unstarred earlier containment gives the same marked critical actor. -/
theorem source_critical_image_le [Finite G] (Vα : Subgroup G)
    (hα : Vα ≤ (one L T V₁ ⊔ T).pCoreIn 2) :
    (Source.starImage H Vα).map geo.equiv.toMonoidHom ≤ MarkedAutomorphisms.pointV.prod ⊥ := by
  rw [← geo.oneT_core_image]
  exact map_mono (star_le_of_le H hα)

open Representation.BinaryOffender
open scoped IsMulCommutative
variable [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsMulCommutative (Source.Utilde H V₃ V₁)]
    [Module (ZMod 2) (Additive (Source.Utilde H V₃ V₁))]

/-- Both literal source commutator identities and the point-residual fixed
seed, under the same product coordinates. Only the actor coordinates change. -/
theorem seed_actions (act : SourceAction H V₃ V₁) :
    subspaceCommutator act.representation (seedSpace H V₃ V₁)
      (Source.starImage H (plus L T V₁)) = seedSpace H V₃ V₁ ∧
    subspaceCommutator act.representation ⊤ (Source.starImage H (plus L T V₁)) = ⊤ ∧
    seedSpace H V₃ V₁ ≤ fixedSpace act.representation (Source.starImage H (zero L)) ∧
    seedSpace H V₃ V₁ ≤ fixedSpace (act.representation.comp geo.equiv.symm.toMonoidHom)
      ((MarkedAutomorphisms.residual pointParabolicSL).prod ⊥) := by
  obtain ⟨hseed,hfull,hfixed⟩ := source_seed_actions H K L T V₁ V₃ eK geo.component act geo.plus_le
  refine ⟨hseed,hfull,hfixed,?_⟩
  intro v hv g
  have hg : g.val ∈ (Source.starImage H (zero L)).map geo.equiv.toMonoidHom := by
    rw [geo.zero_image]
    exact g.property
  obtain ⟨x,hx,hxg⟩ := hg
  change act.representation (geo.equiv.symm g.val) v = v
  rw [← hxg]
  change act.representation (geo.equiv.symm (geo.equiv x)) v = v
  rw [geo.equiv.symm_apply_apply]
  exact hfixed hv ⟨x,hx⟩

end SourceProductGeometry
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct
