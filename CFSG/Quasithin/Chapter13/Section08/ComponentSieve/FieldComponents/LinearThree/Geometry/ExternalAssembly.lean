module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.ExternalComponentAction
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct

/-!
# External-component geometry from the source component list

For ordinary A₆, the component reduction, centralization and seed generation
feed the conjugation-image dichotomy. The exact earlier 13.8.13 applies to
both constructed solvable L₁T-overgroups inside G₁. Since their join contains
K, the inner-image case contradicts K ≰ M. The remaining equivalence with
Aut(L₃(2)) agrees with the actual conjugation action on every component element.

For covered A₆, the component list first constructs K* ≃ L₃(2). Restricting
the actual ambient Sylow subgroup to H supplies the Sylow input for the
covered product theorem. It then constructs the marked product, inverter,
residual placement, seed actions and critical actor in those same coordinates.
Thus neither the component model nor the product marking is an extra premise.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.21(1), printed pp.956–957. The list 13.8.21(2), the genuine earlier
source facts and the actual source action remain explicit. Representation
exclusions and the final L₁ ≤ K assembly belong to the parent task.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry
open ExternalComponentAction
variable {G : Type*} [Group G] [Finite G]

local instance assembled_star_normal (H K : Subgroup G) [(K.subgroupOf H).Normal] :
    (Source.starImage H K).Normal :=
  (inferInstance : (K.subgroupOf H).Normal).map _ (QuotientGroup.mk'_surjective _)

/-- The ordinary branch after using the universal earlier 13.8.13.
The output includes the intrinsic quotient kernel, centralization,
normal generation and the compatible full automorphism quotient. -/
theorem ordinary_source_geometry
    (κ : GroupClass) (H K L L₁ M G₁ V₁ V₃ : Subgroup G) (T : Sylow 2 G)
    (hQTKE : IsSimpleQTKE κ G)
    (d : RankReduction.SourceSetup κ H K L₁ M G₁ T) (hout : ¬ L₁ ≤ K)
    (models : RankReduction.SmallQuotient (K ⧸ pCore 2 K))
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hmarked : L₁ =
      (pResidual 2 ((L ⊔ (T : Subgroup G)) ⊓ normalizer (V₁ : Set G) : Subgroup G)).map
        ((L ⊔ (T : Subgroup G)) ⊓ normalizer (V₁ : Set G) : Subgroup G).subtype)
    (hflag : (T : Subgroup G) ≤ normalizer (V₁ : Set G))
    (horder : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) →
      Nat.card (L₁ ⧸ pCore 2 L₁) = 3)
    (hfull : ⁅L₁, (T : Subgroup G)⁆ = L₁) (hseed : ⁅V₃, L₁⁆ = V₃)
    (hsolvable : ∀ J : Subgroup G, L₁ ⊔ (T : Subgroup G) ≤ J → J ≤ G₁ →
      Group.IsSolvable J → J ≤ M)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsMulCommutative (Source.Utilde H V₃ V₁)]
    [Module (ZMod 2) (Additive (Source.Utilde H V₃ V₁))]
    (act : SourceAction H V₃ V₁) :
    letI : (K.subgroupOf H).Normal := d.normal
    primeRank 3 K = 1 ∧
    (((QuotientGroup.mk' (pCore 2 H)).comp (K.subgroupOf H).subtype).ker =
      pCore 2 (K.subgroupOf H)) ∧
    ∃ e : Source.starImage H K ≃* Matrix.PSL3Two.PSL,
      ⁅L₁, K⁆ ≤ (pCore 2 K).map K.subtype ∧
      Source.starImage H L₁ ≤ centralizer (Source.starImage H K : Set (Source.Hstar H)) ∧
      (Source.starImage H L₁).Normal ∧
      subspaceCommutator act.representation (seedSpace H V₃ V₁)
        (Source.starImage H L₁) = seedSpace H V₃ V₁ ∧
      subspaceCommutator act.representation ⊤ (Source.starImage H L₁) = ⊤ ∧
      (sourceConjugation H K).ker =
        centralizer (Source.starImage H K : Set (Source.Hstar H)) ∧
      ∃ f : (Source.Hstar H ⧸
          centralizer (Source.starImage H K : Set (Source.Hstar H))) ≃*
          MulAut Matrix.PSL3Two.PSL,
        ∀ (a : Source.Hstar H) (k : Source.starImage H K),
          f (QuotientGroup.mk'
            (centralizer (Source.starImage H K : Set (Source.Hstar H))) a)
            (e k) = e (sourceConjugation H K a k) := by
  let : (K.subgroupOf H).Normal := d.normal
  obtain ⟨hrank, e, hc, _, _, _, hcentral, hn, hseed', hgen, hker, _, halt⟩ :=
    ordinary_external_geometry κ H K L L₁ M G₁ V₁ V₃ T hQTKE d hout models eL
      hmarked hflag horder hfull hseed act
  refine ⟨hrank, starProjection_kernel H K d.component.subnormal,
    e, hc, hcentral, hn, hseed', hgen, hker, ?_⟩
  rcases halt with ⟨J₁, J₂, hJ₁, hJ₁G, hJ₂, hJ₂G, hs₁, hs₂, hjoin, _⟩ | hf
  · exact False.elim (d.external ((le_sup_left.trans hjoin).trans
      (sup_le (hsolvable J₁ hJ₁ hJ₁G hs₁) (hsolvable J₂ hJ₂ hJ₂G hs₂))))
  · exact hf

open CoveredProduct CoveredProduct.ResidualPlacement

/-- The covered geometry with K* ≃ L₃(2) and the relative Sylow supplied
by the component-list reduction. All product, subgroup, core and inverter
marks are constructed, with the seed and critical actor using that product. -/
theorem covered_source_geometry
    (κ : GroupClass) (H K L M G₁ V V₁ V₃ Vα : Subgroup G) (T : Sylow 2 G)
    (d : RankReduction.SourceSetup κ H K (one L T V₁) M G₁ T)
    (hout : ¬ one L T V₁ ≤ K)
    (models : RankReduction.SmallQuotient (K ⧸ pCore 2 K))
    (natural : LocalAction.NaturalSetup L T V V₁ V₃)
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    (hNM : normalizer (zero L : Set G) = M)
    (hfit : fittingPreimageResidual H = ⊥ ∨
      (Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
        fittingPreimageResidual H = one L T V₁) ∨
      fittingPreimageResidual H = plus L T V₁)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsMulCommutative (Source.Utilde H V₃ V₁)]
    [Module (ZMod 2) (Additive (Source.Utilde H V₃ V₁))]
    (act : SourceAction H V₃ V₁)
    (hα : Vα ≤ (one L T V₁ ⊔ (T : Subgroup G)).pCoreIn 2) :
    primeRank 3 K = 1 ∧
    (((QuotientGroup.mk' (pCore 2 H)).comp (K.subgroupOf H).subtype).ker =
      pCore 2 (K.subgroupOf H)) ∧
    ∃ (eK : Source.starImage H K ≃* BinaryLinearThree.Group)
      (geo : SourceProductGeometry H K L T V₁ V₃ eK),
      subspaceCommutator act.representation (seedSpace H V₃ V₁)
        (Source.starImage H (plus L T V₁)) = seedSpace H V₃ V₁ ∧
      subspaceCommutator act.representation ⊤ (Source.starImage H (plus L T V₁)) = ⊤ ∧
      seedSpace H V₃ V₁ ≤ fixedSpace act.representation (Source.starImage H (zero L)) ∧
      seedSpace H V₃ V₁ ≤ fixedSpace (act.representation.comp geo.equiv.symm.toMonoidHom)
        ((Matrix.PSL3Two.MarkedAutomorphisms.residual Matrix.PSL3Two.pointParabolicSL).prod ⊥) ∧
      (Source.starImage H Vα).map geo.equiv.toMonoidHom ≤
        Matrix.PSL3Two.MarkedAutomorphisms.pointV.prod ⊥ := by
  let : (K.subgroupOf H).Normal := d.normal
  obtain ⟨hrank, ⟨e⟩⟩ := RankReduction.rank_one_and_model d hout models
  let eK : Source.starImage H K ≃* BinaryLinearThree.Group := e.trans Matrix.PSL3Two.equiv.symm
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans_eq d.generated
  have hS : ((T.subtype hTH : Sylow 2 H) : Subgroup H).map H.subtype = T := by
    rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH]
  have hgen : H = K ⊔ (one L T V₁ ⊔ (T : Subgroup G)) := by
    rw [← d.generated, sup_assoc]
  obtain ⟨geo⟩ := source_product_geometry H K L T V V₁ V₃ M natural hfactor
    hgen hout d.external hNM (T.subtype hTH) hS eK hfit
  obtain ⟨hseed, hfull, hfixed, hpoint⟩ := geo.seed_actions act
  exact ⟨hrank, starProjection_kernel H K d.component.subnormal, eK, geo,
    hseed, hfull, hfixed, hpoint, geo.source_critical_image_le Vα hα⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry
