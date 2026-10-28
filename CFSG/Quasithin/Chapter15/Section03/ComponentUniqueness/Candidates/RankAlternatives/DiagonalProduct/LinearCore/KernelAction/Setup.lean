module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.DiagonalProduct.LinearCore.ActionLift
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Definitions

/-!
# Earlier local inputs for the centralizer-kernel argument

The choices in `CharacteristicTwo.LocalData` do not assert the local
theorems. `SourceSetup` retains those earlier conclusions explicitly,
including the actual Sylow subgroup, relative component, and the
O_{2,Φ} quotient. It contains neither a kernel-action conclusion nor a
root-generation assertion. The two output predicates below isolate those
remaining obligations without importing the independent matrix-image branch.

`CentralSylowCoverage` says that the cubic-generated subgroup of M ∩ L
has odd index after adjoining Z(L). Transfer in the perfect group L then
absorbs Z(L) into that cubic-generated subgroup. `ActionModuloCenter`
controls the other part of the kernel action; it does not say that its
central error lies in the component residual.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.7, 15.3.11--12, 15.3.33 and 15.3.36--37, printed pp.1122--1135.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped commutatorElement

namespace CFSG.Quasithin.Chapter15.Section03.Candidates.LinearCore.KernelAction

variable {G : Type*} [Group G]

/-- Earlier source conclusions, not conclusions of the kernel calculation. -/
structure SourceSetup (d : CharacteristicTwo.LocalData G) (I L : Subgroup G) : Prop where
  outside : I ∈ d.Hplus
  sylow : ∃ P : Sylow 2 I, (P : Subgroup I).map I.subtype = d.S
  component_le : L ≤ I
  component : IsComponent I (L.subgroupOf I)
  odd_core : pPrimeCore 2 I = ⊥
  component_outside : ¬ L ≤ d.M
  orbit_eq : L = localSpan L d.S
  rank_component : primeRank 3 L = 2
  rank_yplus : primeRank 3 d.Yplus = 2
  rank_overgroup : primeRank 3 I ≤ 2
  theta_eq : theta (d.M ⊓ I) = d.Yplus
  normalizer_eq : I ⊓ normalizer (d.Yplus : Set G) = d.M ⊓ I
  quotient_three : IsPGroup 3 (d.Y ⧸ pCore 2 d.Y)
  yplus_quotient_three : IsPGroup 3 (d.Yplus ⧸ pCore 2 d.Yplus)
  intersection_characteristic_two :
    generalizedFitting (d.M ⊓ I : Subgroup G) = pCore 2 (d.M ⊓ I : Subgroup G)
  residual_ne : componentPart d.Yplus L ≠ ⊥
  core_normalizes : d.R ≤ normalizer (L : Set G)
  component_cores_le :
    L.pCoreIn 2 ⊔ (componentPart d.Yplus L).pCoreIn 2 ≤ d.R
  shadow : RankTwo.RankTwoShadow d.Yplus d.S
  characteristic_two_containment : ∀ D : Subgroup G, D ≤ L →
    d.Yplus ⊔ d.S ≤ normalizer (D : Set G) →
    generalizedFitting D = pCore 2 D → D ≤ d.M ⊓ I

/-- The remaining action assertion after allowing a central error in L.
This is an output to prove from the local setup, not an earlier source input. -/
def ActionModuloCenter (Yplus L : Subgroup G) (y : G) : Prop :=
  ∀ c ∈ Yplus, c ∈ centralizer (L : Set G) →
    ⁅c, y⁆ ∈ (center L).map L.subtype

/-- The root-generation obligation used for the central two-cover.
Equivalently, the displayed subgroup contains a Sylow two-subgroup of L. -/
def CentralSylowCoverage (M L : Subgroup G) : Prop :=
  Nat.Coprime 2 ((theta (M ⊓ L)).subgroupOf L ⊔ center L).index

end CFSG.Quasithin.Chapter15.Section03.Candidates.LinearCore.KernelAction
