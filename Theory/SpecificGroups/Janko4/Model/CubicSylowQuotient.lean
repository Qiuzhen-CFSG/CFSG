module
public import Theory.SpecificGroups.Janko4.Model.ElementarySylowFixers
public import Theory.SpecificGroups.Janko4.Model.SylowNormalizer
public import Theory.Mathieu.M24.ValueBoundParabolics.SylowOvergroup
public import Theory.GroupTheory.PGroup.IndexTwoOmegaCenter
public import Theory.GroupTheory.PGroup.OmegaImage
public import Theory.GroupTheory.CoprimeQuotientSubgroups

/-!
# The exact quotient of a cubic Sylow product in J₄

A full Sylow two-subgroup has no larger normalizer in the native model.
An index-three overgroup therefore has quotient S₃ by its two-core, whose
index in the Sylow is exactly two and whose order is 2²⁰. The central omega
subgroup of this core has order at most four. The quotient isomorphism is
marked by the literal Sylow and cubic images, of orders two and three.

The application is the original actor--Sylow product in the exceptional
cubic comparison of Aschbacher--Smith 4.4.3, printed p.623. Identifying the
selected replacement involution as fixed by the original Sylow requires a
further argument. The imported model certificates retain their attribution
and license.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace Janko4
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

/-- The exact two-core quotient, with both subgroup images under the same map. -/
theorem cubic_sylow_quotient
    (S : Sylow 2 Janko4.Model) (B : Subgroup Janko4.Model)
    (hB : Nat.card B = 3)
    (hi : (S : Subgroup Janko4.Model).relIndex (B ⊔ (S : Subgroup Janko4.Model)) = 3) :
    let M := B ⊔ (S : Subgroup Janko4.Model)
    (M.pCoreIn 2).relIndex (S : Subgroup Janko4.Model) = 2 ∧
      Nat.card (pCore 2 M) = 2^20 ∧
      Nat.card (omega₁ (center (pCore 2 M)) (p := 2)) ≤ 4 ∧
      ∃ e : (M ⧸ pCore 2 M) ≃* Equiv.Perm (Fin 3),
        let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 M))
        Nat.card (((S : Subgroup Janko4.Model).subgroupOf M).map q) = 2 ∧
        Nat.card ((B.subgroupOf M).map q) = 3 := by
  let M := B ⊔ (S : Subgroup Janko4.Model)
  let P := S.subtype (show (S : Subgroup Janko4.Model) ≤ M from le_sup_right)
  obtain ⟨e⟩ := symmetricThree_quotient_of_selfNormalizing_sylow S
    (Janko4.sylow_normalizer_eq S).le M le_sup_right hi
  have hindex : (pCore 2 M).index = 6 := by
    change Nat.card (M ⧸ pCore 2 M) = 6
    rw [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm]
    decide
  have hcore : pCore 2 M ≤ (P : Subgroup M) := pCore_isPGroup.le_sylow_of_normal P
  have htwo : (pCore 2 M).relIndex (P : Subgroup M) = 2 := by
    have hh := relIndex_mul_index hcore
    have hPi : (P : Subgroup M).index = 3 := hi
    rw [hPi,hindex] at hh
    omega
  have hPg : Nat.card P = 2^21 :=
    (Nat.card_congr (subgroupOfEquivOfLe (show (S : Subgroup Janko4.Model) ≤ M from
      le_sup_right)).toEquiv).trans (Janko4.OuterReduction.OddIndex.ambient_sylow_card S)
  have hcorecard : Nat.card (pCore 2 M) = 2^20 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup M) (pCore 2 M) (P : Subgroup M) bot_le hcore
    rw [relIndex_bot_left,relIndex_bot_left,htwo,hPg] at hh
    omega
  have hbound : Nat.card (omega₁ (center (pCore 2 M)) (p := 2)) ≤ 4 := by
    let U := (pCore 2 M).subgroupOf (P : Subgroup M)
    let a := subgroupOfEquivOfLe hcore
    let b := subgroupOfEquivOfLe (show (S : Subgroup Janko4.Model) ≤ M from le_sup_right)
    have hh := card_omega_center_le_sq_of_index_two U htwo
    have hcent : Nat.card (center P) = 2 :=
      (Nat.card_congr (centerCongr b).toEquiv).trans (Janko4.sylow_center_card_two S)
    have hc : Nat.card (omega₁ (center P) (p := 2)) ≤ 2 :=
      (omega₁ (center P) (p := 2)).card_le_card_group.trans_eq hcent
    have he : Nat.card (omega₁ (center U) (p := 2)) =
        Nat.card (omega₁ (center (pCore 2 M)) (p := 2)) := by
      exact Nat.card_congr ((centerCongr a).omega 2 1).toEquiv
    rw [he] at hh
    exact hh.trans (by nlinarith)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 M))
  have hk : q.ker = pCore 2 M := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  refine ⟨?_,hcorecard,hbound,e,?_,?_⟩
  · rw [←relIndex_subgroupOf (L := M)
      (show (S : Subgroup Janko4.Model) ≤ M from le_sup_right)]
    change (((pCore 2 M).map M.subtype).comap M.subtype).relIndex (P : Subgroup M) = 2
    rw [comap_map_eq_self_of_injective M.subtype_injective]
    exact htwo
  · rw [←relIndex_ker,hk]
    exact htwo
  · let A := B.subgroupOf M
    have hAc : Nat.card A = 3 :=
      (Nat.card_congr (subgroupOfEquivOfLe (show B ≤ M from le_sup_left)).toEquiv).trans hB
    have hp : IsPGroup 3 A := IsPGroup.of_card (n := 1) hAc
    have hcop : Nat.Coprime 3 (Nat.card q.ker) := by
      rw [hk,hcorecard]
      norm_num
    have hj := injective_comp_subtype_of_coprime_ker q hcop A hp
    have he := (Nat.card_congr (MonoidHom.ofInjective hj).toEquiv).symm.trans hAc
    rwa [MonoidHom.range_comp,range_subtype] at he
end Janko4
