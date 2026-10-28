module

public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Basic
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.OmegaActions
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.OmegaGeneration
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Defs
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.LocalFamilies

/-!
# The sixteen-point exceptional local factor

Failure of genericity supplies a displayed lifted factor whose ambient commutator is not fixed by the distinguished involution. Coprime idempotence identifies its local four-point module with the fixed intersection, and the commuting C3/C2 action theorem forces ambient order sixteen.

This module supports the rank-at-least-two case of Stellmacher (1.6).
The action is on an elementary abelian two-group; the local hypotheses and
minimal-offender conditions are explicit in the declarations that use them.
Source: `refs/latex/stellmacher-n-group.tex`, proof of (1.6), journal pp.18–19.
-/

open scoped Pointwise symmDiff

namespace Stellmacher.SectionOne.RankOneThreeGroupAssembly

universe u v

/-- An order-three factor's four-point commutator inside an invariant
submodule is exactly that submodule's four-point intersection with the
ambient commutator module.  This is the bridge from the recursive local
coordinate to the lower-layer exceptional action theorem. -/
private theorem commutatorAction_inf_card_eq_four_of_restricted_card_four
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (F : Subgroup G) (C : Subgroup V) [IsInvariant F V C]
    (hFcard : Nat.card F = 3)
    (hlocal : Nat.card (commutatorAction F C) = 4) :
    Nat.card (↥(commutatorAction F V ⊓ C)) = 4 := by
  let U : Subgroup V := commutatorAction F V
  let X : Subgroup V := U ⊓ C
  let hUinv : IsInvariant F V U := commutatorAction_isInvariant
  let _ : IsInvariant F V U := hUinv
  let hXinv : IsInvariant F V X := by
    refine ⟨?_⟩
    intro f v
    exact and_congr
      (IsInvariant.invariant (A := F) (G := V) (H := U) f v)
      (IsInvariant.invariant (A := F) (G := V) (H := C) f v)
  let _ : IsInvariant F V X := hXinv
  let hXelem : IsElementaryAbelian 2 X := isElementaryAbelian_subgroup X
  let _ : IsElementaryAbelian 2 X := hXelem
  have hcopFV : Nat.Coprime (Nat.card F) (Nat.card V) := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    rw [hFcard, hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hcompl : IsCompl (FixedPoints.subgroup F V) U :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := V) (A := F) (Group.isSolvable_of_comm fun x y =>
        (IsMulCommutative.is_comm (M := V)).comm x y)
      hcopFV inferInstance
  have hfixFX : FixedPoints.subgroup F X = ⊥ := by
    apply Subgroup.map_injective X.subtype_injective
    rw [fixedPoints_subgroup_map_subtype_eq_inf, Subgroup.map_bot]
    apply le_antisymm
    · intro x hx
      have hxbot : (x : V) ∈
          FixedPoints.subgroup F V ⊓ U := ⟨hx.2, hx.1.1⟩
      rw [hcompl.inf_eq_bot] at hxbot
      simpa using hxbot
    · exact bot_le
  have hcopFX : Nat.Coprime (Nat.card F) (Nat.card X) := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 X).exists_card_eq
    rw [hFcard, hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hcommFX : commutatorAction F X = ⊤ := by
    have hcomplX : IsCompl (FixedPoints.subgroup F X)
        (commutatorAction F X) :=
      isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
        (G := X) (A := F) (Group.isSolvable_of_comm fun x y =>
          (IsMulCommutative.is_comm (M := X)).comm x y)
        hcopFX inferInstance
    rw [hfixFX] at hcomplX
    simpa using hcomplX.sup_eq_top
  have hlocalLeX : (commutatorAction F C).map C.subtype ≤ X :=
    le_inf (commutatorAction_map_subtype_le_ambient C)
      (Subgroup.map_subtype_le _)
  have hXleLocal : X ≤ (commutatorAction F C).map C.subtype := by
    have hmono := commutatorAction_map_subtype_mono
      (A := F) (V := V) X C inf_le_right
    rw [hcommFX] at hmono
    intro x hx
    apply hmono
    exact ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
  have heq : (commutatorAction F C).map C.subtype = X :=
    le_antisymm hlocalLeX hXleLocal
  change Nat.card X = 4
  rw [← heq, Subgroup.card_map_of_injective C.subtype_injective]
  exact hlocal

/-- Failure of genericity already forces the failed lifted order-three
factor to have a sixteen-point ambient commutator module. -/
public theorem exists_exceptional_local_factor_fixed_card_data
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (S : Subgroup G) (hS : IsElementaryAbelian 2 S)
    (hnongeneric : ¬ RankOneAssemblyGenericHypothesis
      (G := G) (V := V) S) :
    ∃ A F : Subgroup G,
      oneAmax (G := G) (V := V) S A ∧
      Nat.card A = 2 ∧
      F ≤ ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), S⁆ ∧
      Nat.card F = 3 ∧
      RankOneLocalFactorCoordinate (G := G) (V := V) S A F ∧
      ¬ commutatorAction F V ≤ FixedPoints.subgroup A V ∧
      Nat.card (↥(commutatorAction F V ⊓ FixedPoints.subgroup A V)) = 4 ∧
      Nat.card (commutatorAction F V) = 2 ^ 4 := by
  simp only [RankOneAssemblyGenericHypothesis,
    RankOneLocalGenericHypothesis] at hnongeneric
  push Not at hnongeneric
  obtain ⟨A, hAmax, hAcard, hA_H, F, hFWA, hFcard,
      hFlocal, hFcoordinate, hFnot⟩ := hnongeneric
  let W_A := ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), S⁆
  let H := W_A ⊔ S
  let A_H := A.subgroupOf H
  let hA_H' : A_H.Normal := by simpa only [A_H, H, W_A] using hA_H
  let _ : A_H.Normal := hA_H'
  let V_A := FixedPoints.subgroup A_H V
  let hV_AinvH : IsInvariant H V V_A := fixedPoints_isInvariant_of_normal A_H
  let _ : IsInvariant H V V_A := hV_AinvH
  have hFH : F ≤ H := by
    exact hFWA.trans le_sup_left
  let hV_AinvF : IsInvariant F V V_A :=
    isInvariant_of_subgroup H F V_A hFH
  let _ : IsInvariant F V V_A := hV_AinvF
  let D : Subgroup (H ⧸ A_H) :=
    (F.subgroupOf H).map (QuotientGroup.mk' A_H)
  have hDomega : oneOmega (G := H ⧸ A_H) (V := V_A) D := by
    simpa only [D, V_A, A_H, H, W_A] using hFlocal
  have hlocalSub :
      Nat.card (commutatorAction (F.subgroupOf H) V_A) = 4 :=
    commutatorAction_lift_card_eq A_H (F.subgroupOf H) D rfl hDomega.2.2
  have hsubEq : commutatorAction (F.subgroupOf H) V_A =
      commutatorAction F V_A :=
    commutatorAction_subgroupOf_eq H F V_A hFH
  have hlocalAmbient : Nat.card (commutatorAction F V_A) = 4 := by
    rw [← hsubEq]
    exact hlocalSub
  have hfixedEq : V_A = FixedPoints.subgroup A V :=
    fixedPoints_subgroup_subgroupOf_eq H A (hAmax.1.trans le_sup_right)
  have hcommFA : ⁅F, A⁆ = ⊥ := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    exact hFWA.trans
      (local_commutator_le_centralizer S A hS hAmax.1)
  have hfixedCard : Nat.card (↥(commutatorAction F V ⊓
      FixedPoints.subgroup A V)) = 4 := by
    have hfixedVA : Nat.card (↥(commutatorAction F V ⊓ V_A)) = 4 :=
      commutatorAction_inf_card_eq_four_of_restricted_card_four
        F V_A hFcard hlocalAmbient
    calc
      Nat.card (↥(commutatorAction F V ⊓
          FixedPoints.subgroup A V)) =
          Nat.card (↥(commutatorAction F V ⊓ V_A)) := by rw [hfixedEq]
      _ = 4 := hfixedVA
  have hnotAmbient : ¬ commutatorAction F V ≤
      FixedPoints.subgroup A V := by
    simpa only [← hfixedEq] using hFnot
  have hcardSixteen :=
    Representation.commutator_card_sixteen_of_commuting_involution_fixed_card_four
      F A hFcard hAcard hcommFA hfixedCard hnotAmbient
  exact ⟨A, F, hAmax, hAcard, hFWA, hFcard, hFcoordinate,
    hnotAmbient, hfixedCard, hcardSixteen⟩

/-- Failure of genericity already forces the failed lifted order-three
factor to have a sixteen-point ambient commutator module. -/
public theorem exists_exceptional_local_factor_card_sixteen
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (S : Subgroup G) (hS : IsElementaryAbelian 2 S)
    (hnongeneric : ¬ RankOneAssemblyGenericHypothesis
      (G := G) (V := V) S) :
    ∃ A F : Subgroup G,
      oneAmax (G := G) (V := V) S A ∧
      Nat.card A = 2 ∧
      F ≤ ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), S⁆ ∧
      Nat.card F = 3 ∧
      RankOneLocalFactorCoordinate (G := G) (V := V) S A F ∧
      ¬ commutatorAction F V ≤ FixedPoints.subgroup A V ∧
      Nat.card (commutatorAction F V) = 2 ^ 4 := by
  obtain ⟨A, F, hAmax, hAcard, hFWA, hFcard, hcoord, hnot, _, hcard⟩ :=
    exists_exceptional_local_factor_fixed_card_data S hS hnongeneric
  exact ⟨A, F, hAmax, hAcard, hFWA, hFcard, hcoord, hnot, hcard⟩

end Stellmacher.SectionOne.RankOneThreeGroupAssembly
