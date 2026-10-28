module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.NaturalFlags.Construction
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.EarlierSource

/-!
# Applying the natural flag to the earlier-source geometry

`source_geometry_of_invariant_flag` supplies the `hN` argument of the existing
geometry assembly from the genuine natural action, with the literal flag,
residuals and conjugate intersection. All four finite automorphism calculations
are discharged. The extraspecial, classification and middle-quotient inputs
retain their existing source owners under `qt-14-04-large-local-action`.
The conditional automorphism-calculation application remains available.

Source: Aschbacher--Smith, 14.4.8(1--2) and 14.4.13, pp.1009,1012.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.NaturalFlags
open Components
variable {G : Type*} [Group G] [Finite G]

/-- Apply the constructed flag to the original earlier-source consumer. -/
noncomputable def source_geometry_of_automorphism_calculation
    (earlier : EarlierComponentGeneration G)
    (T : Sylow 2 G) (hEven : IsEvenCharacteristicAt T)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    {M L V X U Ug Z Zg Wg : Subgroup G} [IsElementaryAbelian 2 V]
    (d : NaturalThreeAction L V T) (F : Chapter12.Section08.InvariantFlag T V 3)
    (g : G) (hg : g ∈ L) [IsElementaryAbelian 2 (F.E g)]
    (hc₁ : Nat.card (coreQuotient (flagResidual ((F.Vi 1).subgroupOf V))) = 3)
    (hc₂ : Nat.card (coreQuotient (flagResidual ((F.Vi 2).subgroupOf V))) = 3)
    (hgen : flagResidual ((F.Vi 1).subgroupOf V) ⊔
      flagResidual ((F.Vi 2).subgroupOf V) = ⊤)
    (hm : flagMovement ((F.Vi 2).subgroupOf V)
      (flagResidual ((F.Vi 1).subgroupOf V)) = ⊤)
    (extraspecial : EarlierExtraspecialData T (F.Vi 2) (F.E g) U Ug Z Zg Wg (F.Li L 2))
    (hX : X ∈ YFamily F.H T (F.Vi 2) (F.E g)) (hne : X ≠ F.Li L 1)
    (e₂ : coreQuotient (F.Li L 1 ⊔ X ⊔ (T : Subgroup G)) ≃* SymmetricThreeProduct.G)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → L ⊔ (T : Subgroup G) ≤ K → K = M)
    (hLM : L ≤ M) (hTM : (T : Subgroup G) ≤ M)
    (hMnorm : M ≤ normalizer (L : Set G)) :
    EarlierSourceResult F.H M L (F.Li L 1) (F.Li L 2) (F.Vi 2) (F.E g) U Ug X T :=
  source_geometry_of_earlier_data earlier T hEven classification extraspecial
    (naturalFlagData_of_automorphism_calculation d F g hg hc₁ hc₂ hgen hm)
    hX hne e₂ hunique hLM hTM hMnorm

/-- The literal source geometry application with the original natural flag
constructed, rather than supplied as a conclusion-bearing hypothesis. -/
noncomputable def source_geometry_of_invariant_flag
    (earlier : EarlierComponentGeneration G)
    (T : Sylow 2 G) (hEven : IsEvenCharacteristicAt T)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    {M L V X U Ug Z Zg Wg : Subgroup G} [IsElementaryAbelian 2 V]
    (d : NaturalThreeAction L V T) (F : Chapter12.Section08.InvariantFlag T V 3)
    (g : G) (hg : g ∈ L) [IsElementaryAbelian 2 (F.E g)]
    (extraspecial : EarlierExtraspecialData T (F.Vi 2) (F.E g) U Ug Z Zg Wg (F.Li L 2))
    (hX : X ∈ YFamily F.H T (F.Vi 2) (F.E g)) (hne : X ≠ F.Li L 1)
    (e₂ : coreQuotient (F.Li L 1 ⊔ X ⊔ (T : Subgroup G)) ≃* SymmetricThreeProduct.G)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → L ⊔ (T : Subgroup G) ≤ K → K = M)
    (hLM : L ≤ M) (hTM : (T : Subgroup G) ≤ M)
    (hMnorm : M ≤ normalizer (L : Set G)) :
    EarlierSourceResult F.H M L (F.Li L 1) (F.Li L 2) (F.Vi 2) (F.E g) U Ug X T :=
  source_geometry_of_earlier_data earlier T hEven classification extraspecial
    (naturalFlagData_of_invariant_flag d F g hg)
    hX hne e₂ hunique hLM hTM hMnorm

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.NaturalFlags
