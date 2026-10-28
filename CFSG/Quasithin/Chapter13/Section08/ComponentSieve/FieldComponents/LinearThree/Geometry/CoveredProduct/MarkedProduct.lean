module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.MarkedProduct.Orientation
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.SourceActions
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.Decomposition
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.Transport
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedProduct

/-!
# The compatible covered product and source subgroup marks

The point-oriented component map and the supplied marked centralizer map
extend through multiplication to one equivalence H* ≃ SL₃(2) × S₃.
The source Sylow intersection supplies its entire Borel factor, while the
corrected source inverter supplies the specified transposition. Sylow
maximality identifies T*, and the source factorizations then identify L₀T,
L₁ and L₁T. Intrinsic two-cores are transported through this same map.

This is a conditional prerequisite for Aschbacher–Smith 13.8.21(1), printed
p.957. The marked centralizer equivalence is an explicit input; the parent
source proof constructs it. No tensor identification or quadratic rank bound
is asserted here.
-/

@[expose] public section
open Subgroup Matrix.PSL3Two
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct
open ResidualPlacement
namespace MarkedProduct

private theorem prod_join {A B : Type*} [Group A] [Group B]
    (P Q : Subgroup A) (R S : Subgroup B) :
    P.prod R ⊔ Q.prod S = (P ⊔ Q).prod (R ⊔ S) := by
  apply le_antisymm
  · exact sup_le (prod_mono le_sup_left le_sup_left) (prod_mono le_sup_right le_sup_right)
  · apply prod_le_iff.mpr
    constructor
    · rw [Subgroup.map_sup]
      apply sup_le
      · rintro _ ⟨x,hx,rfl⟩
        exact mem_sup_left ⟨hx,R.one_mem⟩
      · rintro _ ⟨x,hx,rfl⟩
        exact mem_sup_right ⟨hx,S.one_mem⟩
    · rw [Subgroup.map_sup]
      apply sup_le
      · rintro _ ⟨x,hx,rfl⟩
        exact mem_sup_left ⟨P.one_mem,hx⟩
      · rintro _ ⟨x,hx,rfl⟩
        exact mem_sup_right ⟨Q.one_mem,hx⟩

variable {G : Type*} [Group G]
variable (H K L T V₁ V₃ : Subgroup G)
    (eK : Source.starImage H K ≃* BinaryLinearThree.Group)
    (geo : SourceComponentGeometry H K L T V₁ V₃ eK)

/-- The literal star image of the corrected source inverter. -/
def inverterStar : Source.Hstar H :=
  QuotientGroup.mk' (pCore 2 H) ⟨geo.inverter.val,geo.inverter_mem⟩

/-- Its centralizer membership is derived from the source action identity. -/
theorem inverterStar_mem : inverterStar H K L T V₁ V₃ eK geo ∈
    centralizer (Source.starImage H K : Set (Source.Hstar H)) := by
  intro x hx
  exact (mul_inv_eq_iff_eq_mul.mp (geo.inverter_component_action ⟨x,hx⟩)).symm

variable (eC : centralizer (Source.starImage H K : Set (Source.Hstar H)) ≃* Equiv.Perm (Fin 3))

/-- One equivalence for the component, every local mark and the seed action. -/
noncomputable def equiv : Source.Hstar H ≃* BinaryLinearThree.Group × Equiv.Perm (Fin 3) :=
  productEquiv H K (pointComponentEquiv H K L T eK geo.placement) eC geo.inner_action

/-- The component is the entire first factor. -/
theorem component_image : (Source.starImage H K).map
    (equiv H K L T V₁ V₃ eK geo eC).toMonoidHom =
      (⊤ : Subgroup BinaryLinearThree.Group).prod ⊥ := by
  rw [equiv, productEquiv_component_subgroup H K _ _ _ _ le_rfl,
    subgroupOf_self, map_top_of_surjective _ (pointComponentEquiv H K L T eK geo.placement).surjective]

/-- The full source L₀* is the point residual in the first factor. -/
theorem zero_image : (Source.starImage H (zero L)).map
    (equiv H K L T V₁ V₃ eK geo eC).toMonoidHom =
      (MarkedAutomorphisms.residual pointParabolicSL).prod ⊥ := by
  rw [equiv, productEquiv_component_subgroup H K _ _ _ _ (star_le_of_le H geo.zero_le),
    pointComponentEquiv_residual]

/-- The cubic mark is inherited from the supplied centralizer equivalence. -/
theorem plus_image
    (hC : ((Source.starImage H (plus L T V₁)).subgroupOf
      (centralizer (Source.starImage H K : Set (Source.Hstar H)))).map eC.toMonoidHom =
        alternatingGroup (Fin 3)) :
    (Source.starImage H (plus L T V₁)).map (equiv H K L T V₁ V₃ eK geo eC).toMonoidHom =
      (⊥ : Subgroup BinaryLinearThree.Group).prod (alternatingGroup (Fin 3)) := by
  rw [equiv, productEquiv_centralizer_subgroup H K _ _ _ _
    (le_centralizer_iff.mp geo.plus_centralized), hC]

/-- The chosen transposition is the image of the actual corrected inverter. -/
theorem inverter_image
    (hs : eC ⟨inverterStar H K L T V₁ V₃ eK geo,
      inverterStar_mem H K L T V₁ V₃ eK geo⟩ = Equiv.swap (1 : Fin 3) 2) :
    equiv H K L T V₁ V₃ eK geo eC (inverterStar H K L T V₁ V₃ eK geo) =
      (1,Equiv.swap (1 : Fin 3) 2) := by
  rw [equiv, productEquiv_centralizer H K _ _ _
    ⟨_,inverterStar_mem H K L T V₁ V₃ eK geo⟩, hs]

/-- The actual source Sylow subgroup has the two specified factors. -/
theorem sylow_image [Finite G]
    (hTH : T ≤ H) (S : Sylow 2 H) (hS : (S : Subgroup H).map H.subtype = T)
    (hs : eC ⟨inverterStar H K L T V₁ V₃ eK geo,
      inverterStar_mem H K L T V₁ V₃ eK geo⟩ = Equiv.swap (1 : Fin 3) 2) :
    (Source.starImage H T).map (equiv H K L T V₁ V₃ eK geo eC).toMonoidHom =
      borelSL.prod Matrix.PSL3Two.MarkedProduct.R := by
  let e := equiv H K L T V₁ V₃ eK geo eC
  have hS' : (S : Subgroup H) = T.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hS, map_subgroupOf_eq_of_le hTH]
  have hp : IsPGroup 2 (Source.starImage H T) := by
    change IsPGroup 2 ((T.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)))
    rw [← hS']
    exact S.isPGroup'.map _
  apply Matrix.PSL3Two.MarkedProduct.productSylow.is_maximal' (hp.map e.toMonoidHom)
  apply prod_le_iff.mpr
  constructor
  · rintro _ ⟨b,hb,rfl⟩
    rw [← pointComponentEquiv_sylow H K L T eK geo.placement] at hb
    obtain ⟨k,hk,hkb⟩ := hb
    refine ⟨k.val,hk,?_⟩
    change productEquiv H K (pointComponentEquiv H K L T eK geo.placement) eC
      geo.inner_action k.val = (b,1)
    rw [productEquiv_component]
    exact Prod.ext hkb rfl
  · rw [Matrix.PSL3Two.MarkedProduct.R, MonoidHom.map_zpowers]
    apply zpowers_le.mpr
    refine ⟨inverterStar H K L T V₁ V₃ eK geo,
      ⟨⟨geo.inverter.val,geo.inverter_mem⟩,geo.inverter.property.1,rfl⟩,?_⟩
    exact inverter_image H K L T V₁ V₃ eK geo eC hs

/-- The source factorization also marks L₁* itself. -/
theorem one_image
    (hKH : K ≤ H) (hDH : one L T V₁ ≤ H)
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    (hC : ((Source.starImage H (plus L T V₁)).subgroupOf
      (centralizer (Source.starImage H K : Set (Source.Hstar H)))).map eC.toMonoidHom =
        alternatingGroup (Fin 3)) :
    (Source.starImage H (one L T V₁)).map (equiv H K L T V₁ V₃ eK geo eC).toMonoidHom =
      (MarkedAutomorphisms.residual pointParabolicSL).prod (alternatingGroup (Fin 3)) := by
  have hXH : plus L T V₁ ≤ H := (hfactor ▸ le_sup_left).trans hDH
  rw [hfactor, star_sup H _ _ hXH (geo.zero_le.trans hKH), Subgroup.map_sup,
    plus_image H K L T V₁ V₃ eK geo eC hC, zero_image H K L T V₁ V₃ eK geo eC,
    prod_join, bot_sup_eq, sup_bot_eq]

/-- The source L₀T maps to the point parabolic with the marked involution factor. -/
theorem zeroT_image [Finite G]
    (hKH : K ≤ H) (hTH : T ≤ H)
    (S : Sylow 2 H) (hS : (S : Subgroup H).map H.subtype = T)
    (hs : eC ⟨inverterStar H K L T V₁ V₃ eK geo,
      inverterStar_mem H K L T V₁ V₃ eK geo⟩ = Equiv.swap (1 : Fin 3) 2) :
    (Source.starImage H (zero L ⊔ T)).map (equiv H K L T V₁ V₃ eK geo eC).toMonoidHom =
      pointParabolicSL.prod Matrix.PSL3Two.MarkedProduct.R := by
  rw [star_sup H _ _ (geo.zero_le.trans hKH) hTH, Subgroup.map_sup,
    zero_image H K L T V₁ V₃ eK geo eC,
    sylow_image H K L T V₁ V₃ eK geo eC hTH S hS hs, prod_join,
    Matrix.PSL3Two.MarkedProduct.residual_sup_borel, bot_sup_eq]

/-- L₁T adds the cubic factor and therefore has the entire S₃ factor. -/
theorem oneT_image [Finite G]
    (hKH : K ≤ H) (hDH : one L T V₁ ≤ H) (hTH : T ≤ H)
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    (S : Sylow 2 H) (hS : (S : Subgroup H).map H.subtype = T)
    (hC : ((Source.starImage H (plus L T V₁)).subgroupOf
      (centralizer (Source.starImage H K : Set (Source.Hstar H)))).map eC.toMonoidHom =
        alternatingGroup (Fin 3))
    (hs : eC ⟨inverterStar H K L T V₁ V₃ eK geo,
      inverterStar_mem H K L T V₁ V₃ eK geo⟩ = Equiv.swap (1 : Fin 3) 2) :
    (Source.starImage H (one L T V₁ ⊔ T)).map (equiv H K L T V₁ V₃ eK geo eC).toMonoidHom =
      pointParabolicSL.prod (⊤ : Subgroup (Equiv.Perm (Fin 3))) := by
  rw [star_sup H _ _ hDH hTH, Subgroup.map_sup,
    one_image H K L T V₁ V₃ eK geo eC hKH hDH hfactor hC,
    sylow_image H K L T V₁ V₃ eK geo eC hTH S hS hs, prod_join,
    Matrix.PSL3Two.MarkedProduct.residual_sup_borel, Matrix.PSL3Two.MarkedProduct.alternating_sup_R]

/-- All four intrinsic source cores under the single compatible product map.
In particular O₂(L₀*) is the four-group, and is not discarded. -/
theorem core_images [Finite G]
    (hgen : H = K ⊔ (one L T V₁ ⊔ T))
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    (S : Sylow 2 H) (hS : (S : Subgroup H).map H.subtype = T)
    (hC : ((Source.starImage H (plus L T V₁)).subgroupOf
      (centralizer (Source.starImage H K : Set (Source.Hstar H)))).map eC.toMonoidHom =
        alternatingGroup (Fin 3))
    (hs : eC ⟨inverterStar H K L T V₁ V₃ eK geo,
      inverterStar_mem H K L T V₁ V₃ eK geo⟩ = Equiv.swap (1 : Fin 3) 2) :
    (Source.starImage H ((zero L).pCoreIn 2)).map
        (equiv H K L T V₁ V₃ eK geo eC).toMonoidHom = MarkedAutomorphisms.pointV.prod ⊥ ∧
    (Source.starImage H (T.pCoreIn 2)).map
        (equiv H K L T V₁ V₃ eK geo eC).toMonoidHom = borelSL.prod Matrix.PSL3Two.MarkedProduct.R ∧
    (Source.starImage H ((zero L ⊔ T).pCoreIn 2)).map
        (equiv H K L T V₁ V₃ eK geo eC).toMonoidHom =
          MarkedAutomorphisms.pointV.prod Matrix.PSL3Two.MarkedProduct.R ∧
    (Source.starImage H ((one L T V₁ ⊔ T).pCoreIn 2)).map
        (equiv H K L T V₁ V₃ eK geo eC).toMonoidHom = MarkedAutomorphisms.pointV.prod ⊥ := by
  have hKH : K ≤ H := by rw [hgen]; exact le_sup_left
  have hDH : one L T V₁ ≤ H := by rw [hgen]; exact le_sup_left.trans le_sup_right
  have hTH : T ≤ H := by rw [hgen]; exact le_sup_right.trans le_sup_right
  refine ⟨?_,?_,?_,?_⟩
  · rw [marked_twoCore_image H _ (geo.zero_le.trans hKH),
      zero_image H K L T V₁ V₃ eK geo eC, Matrix.PSL3Two.MarkedProduct.residual_product_core]
  · rw [marked_twoCore_image H _ hTH,
      sylow_image H K L T V₁ V₃ eK geo eC hTH S hS hs,
      Matrix.PSL3Two.MarkedProduct.sylow_product_core]
  · rw [marked_twoCore_image H _ (sup_le (geo.zero_le.trans hKH) hTH),
      zeroT_image H K L T V₁ V₃ eK geo eC hKH hTH S hS hs,
      Matrix.PSL3Two.MarkedProduct.point_sylow_product_core]
  · rw [marked_twoCore_image H _ (sup_le hDH hTH),
      oneT_image H K L T V₁ V₃ eK geo eC hKH hDH hTH hfactor S hS hC hs,
      Matrix.PSL3Two.MarkedProduct.point_full_product_core]

/-- Transport the earlier starred critical containment, with no rank inference.
The later critical-pair representation hypotheses are still required. -/
theorem critical_image_le_pointV [Finite G]
    (hgen : H = K ⊔ (one L T V₁ ⊔ T))
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    (S : Sylow 2 H) (hS : (S : Subgroup H).map H.subtype = T)
    (hC : ((Source.starImage H (plus L T V₁)).subgroupOf
      (centralizer (Source.starImage H K : Set (Source.Hstar H)))).map eC.toMonoidHom =
        alternatingGroup (Fin 3))
    (hs : eC ⟨inverterStar H K L T V₁ V₃ eK geo,
      inverterStar_mem H K L T V₁ V₃ eK geo⟩ = Equiv.swap (1 : Fin 3) 2)
    (Vα : Subgroup G)
    (hα : Source.starImage H Vα ≤ (Source.starImage H (one L T V₁ ⊔ T)).pCoreIn 2) :
    (Source.starImage H Vα).map (equiv H K L T V₁ V₃ eK geo eC).toMonoidHom ≤
      MarkedAutomorphisms.pointV.prod ⊥ := by
  have hKH : K ≤ H := by rw [hgen]; exact le_sup_left
  have hDH : one L T V₁ ≤ H := by rw [hgen]; exact le_sup_left.trans le_sup_right
  have hTH : T ≤ H := by rw [hgen]; exact le_sup_right.trans le_sup_right
  have hm := map_mono (f := (equiv H K L T V₁ V₃ eK geo eC).toMonoidHom) hα
  rw [map_pCoreIn_of_injective 2 _ _ (equiv H K L T V₁ V₃ eK geo eC).injective,
    oneT_image H K L T V₁ V₃ eK geo eC hKH hDH hTH hfactor S hS hC hs,
    Matrix.PSL3Two.MarkedProduct.point_full_product_core] at hm
  exact hm

/-- The unstarred containment of 13.8.8 also suffices, through the actual core map. -/
theorem source_critical_image_le_pointV [Finite G]
    (hgen : H = K ⊔ (one L T V₁ ⊔ T))
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    (S : Sylow 2 H) (hS : (S : Subgroup H).map H.subtype = T)
    (hC : ((Source.starImage H (plus L T V₁)).subgroupOf
      (centralizer (Source.starImage H K : Set (Source.Hstar H)))).map eC.toMonoidHom =
        alternatingGroup (Fin 3))
    (hs : eC ⟨inverterStar H K L T V₁ V₃ eK geo,
      inverterStar_mem H K L T V₁ V₃ eK geo⟩ = Equiv.swap (1 : Fin 3) 2)
    (Vα : Subgroup G) (hα : Vα ≤ (one L T V₁ ⊔ T).pCoreIn 2) :
    (Source.starImage H Vα).map (equiv H K L T V₁ V₃ eK geo eC).toMonoidHom ≤
      MarkedAutomorphisms.pointV.prod ⊥ := by
  apply critical_image_le_pointV H K L T V₁ V₃ eK geo eC hgen hfactor S hS hC hs Vα
  rw [← starImage_twoCore H _ (by rw [hgen]; exact le_sup_right)]
  exact star_le_of_le H hα

open Representation.BinaryOffender
open scoped IsMulCommutative
variable [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsMulCommutative (Source.Utilde H V₃ V₁)]
    [Module (ZMod 2) (Additive (Source.Utilde H V₃ V₁))]

/-- The fixed seed for L₀* is now the fixed seed for the point residual.
Only actor coordinates change: the representation is the literal source
conjugation action and the vector subspace remains the literal `seedSpace`. -/
theorem seed_fixed_point_residual (act : SourceAction H V₃ V₁) :
    seedSpace H V₃ V₁ ≤ fixedSpace
      (act.representation.comp (equiv H K L T V₁ V₃ eK geo eC).symm.toMonoidHom)
      ((MarkedAutomorphisms.residual pointParabolicSL).prod ⊥) := by
  have hf := seed_fixed_of_group_commutator H V₃ V₁ act (zero L) geo.seed_zero_fixed
  intro v hv g
  have hg : g.val ∈ (Source.starImage H (zero L)).map
      (equiv H K L T V₁ V₃ eK geo eC).toMonoidHom := by
    rw [zero_image H K L T V₁ V₃ eK geo eC]
    exact g.property
  obtain ⟨x,hx,hxg⟩ := hg
  have he : (equiv H K L T V₁ V₃ eK geo eC).symm g.val = x := by
    rw [← hxg]
    exact (equiv H K L T V₁ V₃ eK geo eC).symm_apply_apply x
  change act.representation ((equiv H K L T V₁ V₃ eK geo eC).symm g.val) v = v
  rw [he]
  exact hf hv ⟨x,hx⟩

end MarkedProduct
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct
