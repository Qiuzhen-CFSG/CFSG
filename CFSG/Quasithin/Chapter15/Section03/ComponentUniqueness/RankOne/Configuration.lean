module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Quotient

/-!
# The output to be constructed before the model exclusions

`ReducedConfiguration` specifies the subgroup and action data at the end
of the first part of 15.3.43. It keeps the original groups as well as the
quotient: the final contradictions concern `C_S(Y₊)`, `C_S(L)`, and `Y₊`
itself, so quotient information alone is insufficient.

This is a shared output contract for the reduction and the independent
model calculations. It is deliberately not called a source hypothesis,
and no projection from it is asserted as a proof of 15.3.43. The theorem's
assembly must construct the record from the earlier source results and
the assumed S₃ shadow, then discharge every model case.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.43(a)--(e), printed pp.1139--1140; the component and odd-core inputs
are 15.3.25 and 15.3.33.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.RankOne

open Subgroup

variable {G : Type*} [Group G]

/-- The reduction output consumed by the model exclusions. Every normality
assertion is relative to its indicated overgroup, and the quotient is the
actual quotient by `C_I(L)`. The model alternative from 1.1.5(3) remains
separate and must use a multiplicative equivalence with a concrete carrier. -/
structure ReducedConfiguration (Yplus S M I L V₁ V₂ : Subgroup G) : Prop
    extends ComponentAction I L where
  minimal : I ∈ minimalOutsideFamily Yplus S M
  sylow : ∃ P : Sylow 2 I, (P : Subgroup I).map I.subtype = S
  sylow_le_M : S ≤ M
  component : Theory.GroupTheory.IsComponent I (L.subgroupOf I)
  oddCore : pPrimeCore 2 I = ⊥
  component_center : (center L).map L.subtype = L.pCoreIn 2
  component_outside : ¬ L ≤ M
  generated : I = L ⊔ S
  y_le_component : Yplus ≤ L
  residual : Yplus = threeResidualIn (M ⊓ I)
  index : (pCore 2 Yplus).index = 3
  theta_eq : theta (M ⊓ I) = Yplus
  normalizer_eq : I ⊓ normalizer (Yplus : Set G) = M ⊓ I
  local_fitting : Theory.GroupTheory.generalizedFitting (M ⊓ I : Subgroup G) =
    pCore 2 (M ⊓ I : Subgroup G)
  shadow : SymmetricThreeShadow Yplus S
  plane_one_le : V₁ ≤ S
  plane_two_le : V₂ ≤ S
  plane_one_centralizes : ⁅V₁, Yplus⁆ = ⊥
  plane_one_acts : ⁅V₁, L⁆ ≠ ⊥
  plane_two_elementary : IsElementaryAbelian 2 V₂
  plane_two_card : Nat.card V₂ = 4
  plane_two_commutator : ⁅V₂, Yplus⁆ = V₂
  plane_two_normalized : M ⊓ I ≤ normalizer (V₂ : Set G)
  not_alternating_four : ¬ Nonempty (Yplus ≃* alternatingGroup (Fin 4))
  quotient : QuotientConditions toComponentAction Yplus S M

end CFSG.Quasithin.Chapter15.Section03.RankOne
