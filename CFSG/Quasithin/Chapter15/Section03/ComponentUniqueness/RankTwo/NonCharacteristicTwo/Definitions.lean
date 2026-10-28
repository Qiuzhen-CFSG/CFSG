module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Reductions

/-!
# Earlier inputs for the non-characteristic-two branches

`ComponentSetup` collects the actual component, its relative normality and
centralizer quotient, and the preceding subgroup conclusions. The source
catalogue is supplied separately through its concrete model equivalences.
`ActionSetup` retains the genuine Hypothesis 15.3.10 dichotomy and the ambient
four-space. Its radical is O₂(Y₊S), and its center is formed inside that radical.

These are input interfaces, not existence or classification assertions. Every
field comes from the standing setup or a result preceding 15.3.42; the local
model recognition and commutator-order calculation remain to be proved.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 15.3.2,
15.3.7, 15.3.10--11, 15.3.33, 15.3.36 and 15.3.39--42,
printed pp.1120--1124 and 1134--1138.
-/

public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo
variable {G : Type*} [Group G]
/-- Inputs from 15.3.11, 15.3.33, 15.3.36 and 15.3.39--41.
The family and centralizer quotient are literal subgroups and quotients. -/
structure ComponentSetup (I L M Yplus S : Subgroup G) [(L.subgroupOf I).Normal] : Prop where
  component_le : L ≤ I
  component_quasisimple : IsQuasisimple L
  join_eq : I = L ⊔ S
  yplus_le : Yplus ≤ L
  outside : ¬ L ≤ M
  sylow_le_M : S ≤ M
  minimal : I ∈ minimalOutsideFamily Yplus S M
  sylow : ∃ P : Sylow 2 I, (P : Subgroup I).map I.subtype = S
  oddCore : pPrimeCore 2 L = ⊥
  center_eq : center L = pCore 2 L
  normalizer_eq : I ⊓ normalizer (Yplus : Set G) = M ⊓ I
  theta_eq : theta (M ⊓ I) = Yplus
  intersection_fitting : generalizedFitting (M ⊓ I : Subgroup G) = pCore 2 (M ⊓ I : Subgroup G)
  yplus_twoResidual : Stellmacher.twoResidualAmbient Yplus = Yplus
  yplus_three_rank : primeRank 3 Yplus = 2
  yplus_exponent : ∀ x : Yplus ⧸ pCore 2 Yplus, x ^ 3 = 1
  shadow : RankTwoShadow Yplus S
  simple_image : IsSimpleGroup (componentImage I L L)
  fitting_eq : generalizedFitting (ComponentQuotient I L) = componentImage I L L
  quotient_local : LocalConfiguration (componentImage I L L) (componentImage I L M)
    (componentImage I L Yplus) (componentImage I L S)

/-- The original four-dimensional module, its two planes, and earlier action
facts. The order of [V,Y₊] and the J₂ centralizer calculation are not fields. -/
structure ActionSetup (M Y S V V₁ V₂ Yplus : Subgroup G) : Prop where
  hypothesis : Hypothesis15310 M Y S V₁ Yplus
  elementary : IsElementaryAbelian 2 V
  card : Nat.card V = 16
  moved : ⁅V, Y⁆ = V
  le_sylow : V ≤ S
  first_le : V₁ ≤ V
  second_le : V₂ ≤ V
  first_card : Nat.card V₁ = 4
  second_card : Nat.card V₂ = 4
  plane_join : V₁ ⊔ V₂ = V
  plane_disjoint : V₁ ⊓ V₂ = ⊥
  normalized : M ≤ normalizer (V : Set G)
  central_radical : V ≤ (center ((Yplus ⊔ S : Subgroup G).pCoreIn 2)).map
    ((Yplus ⊔ S : Subgroup G).pCoreIn 2).subtype
  caseTwo_moved : CaseTwo M Y S V₁ Yplus → ⁅V, Yplus⁆ = V₂
  normalizer_control : CaseTwo M Y S V₁ Yplus → normalizer (V₁ : Set G) ≤ M
end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo
