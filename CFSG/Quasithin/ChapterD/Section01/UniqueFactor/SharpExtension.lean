module
public import CFSG.Quasithin.ChapterD.Section01.UniqueFactor.Setup
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.Basic
public import Theory.GroupTheory.ElementaryThompsonSharpExtension
public import Theory.Representation.BinaryInternalFixedSpaceCodimension.Action
public import Theory.Representation.BinaryInternalFixedSpaceCodimension.Rank

/-!
# Sharp bounds for literal conjugation images

The fixed-space codimension and actor-image cardinality equal the original
centralizer indices. Absence of strong offenders therefore supplies the
sharp inequality used in the maximum elementary fixed-supplement theorem.
All maps are the original normalizer action, with no ambient normality
assumption on the module.

Source application: Aschbacher--Smith, 10.2.8, printed p.749, using B.2.4.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- Linear fixed codimension equals the original subgroup rank difference. -/
theorem image_fixedCodim (H V A : Subgroup G) [IsElementaryAbelian 2 V]
    (hHV : H ≤ normalizer (V : Set G)) (hAH : A ≤ H) :
    fixedCodim (imageRepresentation H V hHV)
      ((A.subgroupOf H).map (show H →* internalActionImage H V hHV from (actionHom H V hHV).rangeRestrict)) =
      Nat.log 2 (Nat.card V) - Nat.log 2 (Nat.card (V ⊓ centralizer (A : Set G) : Subgroup G)) := by
  rw [BinaryInternalFixedSpaceCodimension.fixedCodim_eq_finrank V H A hHV hAH]
  unfold fixedCodim
  rw [←fixedSpace_comp_map]
  rfl

omit [Finite G] in
/-- The literal action image has the original centralizer index. -/
theorem image_card (H V A : Subgroup G)
    (hHV : H ≤ normalizer (V : Set G)) (hAH : A ≤ H) :
    Nat.card ((A.subgroupOf H).map (show H →* internalActionImage H V hHV from (actionHom H V hHV).rangeRestrict)) =
      (centralizer (V : Set G)).relIndex A := by
  change Nat.card ((A.subgroupOf H).map (actionHom H V hHV).rangeRestrict) = _
  rw [←relIndex_ker,MonoidHom.ker_rangeRestrict,actionHom_ker,relIndex_subgroupOf hAH]

/-- No strong offender gives the sharp inequality for the original relative indices. -/
theorem image_not_strong_index_bound (H V A : Subgroup G)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 A]
    (hHV : H ≤ normalizer (V : Set G)) (hAH : A ≤ H)
    (hn : ¬ IsStrongFFModule (imageRepresentation H V hHV)) :
    (centralizer (V : Set G)).relIndex A ≤ (centralizer (A : Set G)).relIndex V := by
  let B : Subgroup (internalActionImage H V hHV) := (A.subgroupOf H).map (show H →* internalActionImage H V hHV from (actionHom H V hHV).rangeRestrict)
  let : IsElementaryAbelian 2 (A.subgroupOf H) := IsElementaryAbelian.subgroupOf hAH
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have hb : rank B ≤ fixedCodim (imageRepresentation H V hHV) B := by
    by_cases he : B=⊥
    · rw [he]; simp [rank]
    · exact Nat.le_of_not_gt (fun hh => hn ⟨B,⟨he,inferInstance⟩,hh⟩)
  have hc := image_card H V A hHV hAH
  have hd := image_fixedCodim H V A hHV hAH
  rw [BinaryInternalFixedSpaceCodimension.rank_eq_log_index] at hd
  change Nat.log 2 (Nat.card B) ≤ _ at hb
  rw [hd,hc] at hb
  have hp : (centralizer (V : Set G)).relIndex A =
      2 ^ Nat.log 2 ((centralizer (V : Set G)).relIndex A) := by
    rw [←hc]
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 B).exists_card_eq
    change Nat.card B = _
    rw [hn,Nat.log_pow (by decide : 1<2)]
  have hp' : (centralizer (A : Set G)).relIndex V =
      2 ^ Nat.log 2 ((centralizer (A : Set G)).relIndex V) := by
    rw [relIndex_eq_two_pow_quotient_finrank, Nat.log_pow (by decide : 1<2)]
  rw [hp,hp']
  exact Nat.pow_le_pow_right (by decide) hb
/-- A maximum elementary subgroup fixes an elementary extension modulo a
sharp submodule when the original submodule kernel already fixes the extension. -/
theorem maxElementary_supplement_of_image_not_strong (S H V W A : Subgroup G)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 W]
    (hHV : H ≤ normalizer (V : Set G)) (hAH : A ≤ H)
    (hVW : V ≤ W) (hWS : W ≤ S)
    (hA : A ∈ Stellmacher.elementaryAbelianMaxSubgroups S)
    (hkernel : A ⊓ centralizer (V : Set G) ≤ centralizer (W : Set G))
    (hn : ¬ IsStrongFFModule (imageRepresentation H V hHV)) :
    W = (W ⊓ centralizer (A : Set G)) ⊔ V := by
  let : IsElementaryAbelian 2 A := hA.2.1
  exact Theory.GroupTheory.maxElementary_fixed_supplement S V W A hVW hWS hA hkernel
    (image_not_strong_index_bound H V A hHV hAH hn)
end CFSG.Quasithin.ChapterD.UniqueFactor
