module
public import CFSG.Quasithin.Chapter2.Section05.OrderTwoCore.PGLNineSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.EarlyCoreSource
public import Theory.SpecificGroups.AlternatingSix.CommutingLocalRank
/-!
# The original PGL₂(9) core branch without an order hypothesis

The actual A6 component is normal in H by quasithinness. The selected
largest-pair argument excludes an order-two core, and the source central
line makes its order greater than two. The already proved nonabelian-core
arguments now give the dihedral core model and the
original crossing marks, with no extra core-order or normality premise.
Source: Aschbacher--Smith 2.5.21, printed pp.565--567.
-/
public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory ComponentRefinement
variable {G : Type*} [Group G] [Finite G]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The original PGL₂(9) branch constructs its nonabelian dihedral core model. -/
theorem MathieuSourceSetup.pgl_nine_source_twoCore_model
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (eK : K ≃* AlternatingSix.ShadowLocal.A6)
    (eQ : (H ⧸ pCore 2 H) ≃* GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F) :
    ∃ k : ℕ, 2 ≤ k ∧ Nonempty (twoCore H ≃* DihedralGroup (2 ^ k)) := by
  let D := K.subgroupOf H
  let eD := (subgroupOfEquivOfLe c.component_le).trans eK
  let : D.Normal := alternatingGroup.normal_of_component_a6_of_quasithin
    (hG.quasithin.subgroup H) D eD c.component
  have hne := MathieuSourceSetup.pgl_nine_twoCore_card_ne_two c hG hempty hgen hb hstar eK eQ
  have hlarge := MathieuSourceSetup.two_lt_core_card_of_ne_two c hG hempty hgen hb hne
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card Atlas.Comparisons.Exceptional.Nine.F) :=
    ⟨3, 2, by decide, by decide, by decide, Atlas.Comparisons.Exceptional.Nine.card⟩
  exact MathieuSourceSetup.pgl_nonabelian_twoCore_model c hgen hodd eQ
    (MathieuSourceSetup.alternating_pgl_source_twoCore_noncommutative c hG hempty hgen hb eK eQ hlarge)

/-- The original PGL₂(9) branch constructs the actual involutions and crossing
element consumed by the remaining component-centralizer contradiction. -/
theorem MathieuSourceSetup.pgl_nine_source_core_crossing
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (eK : K ≃* AlternatingSix.ShadowLocal.A6)
    (eQ : (H ⧸ pCore 2 H) ≃* GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F) :
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
  have hne := MathieuSourceSetup.pgl_nine_twoCore_card_ne_two c hG hempty hgen hb hstar eK eQ
  exact MathieuSourceSetup.alternating_pgl_large_core_crossing c hG hempty hgen hb eK eQ
    (MathieuSourceSetup.two_lt_core_card_of_ne_two c hG hempty hgen hb hne)
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
