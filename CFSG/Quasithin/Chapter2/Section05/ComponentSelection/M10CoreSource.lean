module
public import CFSG.Quasithin.Chapter2.Section05.OrderTwoCore.M10Source
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.EarlyCoreSource
public import Theory.SpecificGroups.AlternatingSix.CommutingLocalRank
/-!
# The original M10 core branch without an order hypothesis

The actual A6 component is normal in H by quasithinness. The selected
largest-pair argument excludes an order-two core, and the source central
line makes its order greater than two. The already proved nonabelian-core
and quaternion arguments now give the precise remaining models and the
original crossing marks, with no extra core-order or normality premise.
Source: Aschbacher--Smith 2.5.21, printed pp.565--567.
-/
public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory ComponentRefinement
variable {G : Type*} [Group G] [Finite G]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The original M10 branch constructs its two remaining core models. -/
theorem MathieuSourceSetup.m10_source_twoCore_models
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (eK : K ≃* AlternatingSix.ShadowLocal.A6)
    (eQ : (H ⧸ pCore 2 H) ≃* AlternatingSix.M10.extension) :
    Nonempty (twoCore H ≃* DihedralGroup 4) ∨
      Nonempty (twoCore H ≃* Semidihedral.StandardModel 4 (by decide)) := by
  let D := K.subgroupOf H
  let eD := (subgroupOfEquivOfLe c.component_le).trans eK
  let : D.Normal := alternatingGroup.normal_of_component_a6_of_quasithin
    (hG.quasithin.subgroup H) D eD c.component
  have hne := MathieuSourceSetup.m10_twoCore_card_ne_two c hG hempty hgen hb hstar eQ
  exact MathieuSourceSetup.m10_large_twoCore_models c hG hempty hgen hb eK eQ
    (MathieuSourceSetup.two_lt_core_card_of_ne_two c hG hempty hgen hb hne)

/-- The original M10 branch constructs the actual involutions and crossing
element consumed by the remaining component-centralizer contradiction. -/
theorem MathieuSourceSetup.m10_source_core_crossing
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (eK : K ≃* AlternatingSix.ShadowLocal.A6)
    (eQ : (H ⧸ pCore 2 H) ≃* AlternatingSix.M10.extension) :
    ∃ t zK x : G, orderOf t = 2 ∧ orderOf zK = 2 ∧ t ∈ twoCore H ∧
      zK ∈ K ∧ x ∈ c.T ∧ x ∉ (S : Subgroup H).map H.subtype ∧
      x ∈ normalizer ((S : Subgroup H).map H.subtype : Set G) ∧
      x ^ 2 ∈ (S : Subgroup H).map H.subtype ∧
      x⁻¹ * t * x = zK ∧ z = t * zK ∧ z ≠ zK ∧ ¬ IsConj t z ∧
      H ≤ centralizer ({t} : Set G) ∧
      ∃ P : Sylow 2 (centralizer ({t} : Set G)),
        (P : Subgroup (centralizer ({t} : Set G))).map (centralizer ({t} : Set G)).subtype =
          (S : Subgroup H).map H.subtype := by
  let D := K.subgroupOf H
  let eD := (subgroupOfEquivOfLe c.component_le).trans eK
  let : D.Normal := alternatingGroup.normal_of_component_a6_of_quasithin
    (hG.quasithin.subgroup H) D eD c.component
  have hne := MathieuSourceSetup.m10_twoCore_card_ne_two c hG hempty hgen hb hstar eQ
  exact MathieuSourceSetup.m10_large_core_crossing c hG hempty hgen hb eK eQ
    (MathieuSourceSetup.two_lt_core_card_of_ne_two c hG hempty hgen hb hne)
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
