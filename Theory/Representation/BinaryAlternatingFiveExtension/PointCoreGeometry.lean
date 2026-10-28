module
public import Theory.Representation.BinaryAlternatingFiveExtension.PointCoreGeometry.Coordinates
public import Theory.GroupTheory.SylowKernelCore
/-!
# Two-core geometry in the natural binary A₄ extension

The literal two-core Rz has order 64, and the two-core of the two-residual
is the extraspecial subgroup R* of order 32. The centralizer of R* in Rz
is its central line; its centralizer modulo that line is exactly R*.
The original vector subgroup has commutator three-space with the residual,
and the commutator of Rz with that residual is all of R*.

The upper commutator bounds follow from the two normal subgroups. For the
reverse bounds, the known Borel difference generators give the three-space,
and the regular four-group consists of commutators with one fixed 3-cycle.
The finite centralizer certificates are isolated in Coordinates.

Source: Aschbacher–Smith, proof of 14.6.9(i,l), printed p.1027.
-/
@[expose] public section


namespace BinaryPermutation.AlternatingFiveExtension.PointCoreGeometry
open Subgroup AlternatingFiveFlag AlternatingFiveBorel
open scoped commutatorElement
local instance : DecidablePred (· ∈ B) := fun g => inferInstanceAs (Decidable (g.val 4 = 4))
local instance : Fintype B := Subtype.fintype _
local instance : Fintype BorelModel := Fintype.ofEquiv _ SemidirectProduct.equivProd.symm
local instance : DecidableEq BorelModel := SemidirectProduct.equivProd.injective.decidableEq
local instance : DecidablePred (· ∈ outerCore) := fun x =>
  inferInstanceAs (Decidable (x.right.val.val ∈ four))
local instance : Fintype outerCore := Subtype.fintype _

@[simp] theorem mem_fixedLine (x : BorelModel) : x ∈ fixedLine ↔ x = 1 ∨ x = centralElement.val := by
  constructor
  · rintro ⟨v,hv,rfl⟩
    rcases hv with rfl | rfl
    · exact Or.inl (map_one _)
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact fixedLine.one_mem
    · exact mem_map_of_mem _ (show Multiplicative.ofAdd FiveCentralizerGeometry.z ∈ line from Or.inr rfl)

theorem fixedLine_le_coreModel : fixedLine ≤ coreModel := by
  rintro x ⟨v,hv,rfl⟩
  exact ⟨line_le_three hv, four.one_mem⟩

theorem coreModel_le_outerCore : coreModel ≤ outerCore := fun _ hx => hx.2

theorem fixedLine_le_center : fixedLine ≤ center BorelModel := by
  intro x hx
  rcases (mem_fixedLine x).mp hx with rfl | rfl
  · exact (center BorelModel).one_mem
  · apply mem_center_iff.mpr
    intro y
    apply SemidirectProduct.ext
    · change y.left * (coreAction y.right.val.val) (Multiplicative.ofAdd FiveCentralizerGeometry.z) =
        Multiplicative.ofAdd FiveCentralizerGeometry.z * y.left
      have hz := congrArg Multiplicative.ofAdd ((fixes_z_iff y.right.val.val).mpr y.right.property)
      change (coreAction y.right.val.val) (Multiplicative.ofAdd FiveCentralizerGeometry.z) =
        Multiplicative.ofAdd FiveCentralizerGeometry.z at hz
      rw [hz,mul_comm]
    · change y.right * 1 = 1 * y.right
      simp

instance fixedLine_normal : fixedLine.Normal where
  conj_mem x hx g := by
    rw [mem_center_iff.mp (fixedLine_le_center hx) g, mul_inv_cancel_right]
    exact hx

theorem fixedLine_card : Nat.card fixedLine = 2 := by
  rw [fixedLine, card_map_of_injective SemidirectProduct.inl_injective, line_card]

theorem center_coreModel_image : (center coreModel).map coreModel.subtype = fixedLine := by
  symm
  apply eq_of_le_of_card_ge
  · intro x hx
    refine ⟨⟨x,fixedLine_le_coreModel hx⟩,?_,rfl⟩
    exact mem_center_iff.mpr (fun y => Subtype.ext (mem_center_iff.mp (fixedLine_le_center hx) y))
  · rw [card_map_of_injective coreModel.subtype_injective,card_center_coreModel,fixedLine_card]

theorem outerCore_centralizer_coreModel : outerCore ⊓ centralizer (coreModel : Set BorelModel) = fixedLine := by
  apply le_antisymm
  · intro x hx
    exact (mem_fixedLine x).mpr (centralizer_cases ⟨x,hx.1⟩ hx.2)
  · exact le_inf (fixedLine_le_coreModel.trans coreModel_le_outerCore)
      (fixedLine_le_center.trans (center_le_centralizer _))

theorem outerCore_centralizerModulo_coreModel : centralizerModulo outerCore coreModel fixedLine = coreModel := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hx,hc⟩ := mem_centralizerModulo_iff.mp hx
    exact modulo_cases ⟨x,hx⟩ (fun a ha => (mem_fixedLine _).mp (hc a ha))
  · intro x hx
    apply mem_centralizerModulo_iff.mpr
    refine ⟨coreModel_le_outerCore hx,fun a ha => ?_⟩
    let : IsExtraspecial 2 coreModel := coreModel_extraspecial
    have hc : ⁅(⟨a,ha⟩ : coreModel),⟨x,hx⟩⁆ ∈ center coreModel :=
      (IsExtraspecial.quotient_elementary_abelian 2 coreModel).commutator_le_center_of_central_quotient
        (commutator_mem_commutator (mem_top _) (mem_top _))
    rw [←center_coreModel_image]
    exact mem_map_of_mem coreModel.subtype hc

instance outerCore_normal : outerCore.Normal where
  conj_mem x hx g := (normalizes_four_of_fixes g.right.val.val g.right.property x.right.val.val).mp hx

theorem outerCore_card : Nat.card outerCore = 64 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem model_card : Nat.card BorelModel = 192 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem pCore_eq_outerCore : pCore 2 BorelModel = outerCore := by
  let S : Sylow 2 BorelModel := Sylow.ofCard outerCore (by
    rw [outerCore_card,model_card]; decide +kernel)
  let : (S : Subgroup BorelModel).Normal := inferInstanceAs outerCore.Normal
  apply le_antisymm (pCore_isPGroup.le_sylow_of_normal S)
  exact le_sSup ⟨inferInstance, IsPGroup.of_card (n := 6) outerCore_card⟩

theorem residual_pCoreIn_eq_coreModel : (pResidual 2 BorelModel).pCoreIn 2 = coreModel := by
  rw [residualModel_eq,pCoreIn,core_residualModel,map_subgroupOf_eq_of_le coreModel_le_residual]
end BinaryPermutation.AlternatingFiveExtension.PointCoreGeometry

namespace BinaryPermutation.AlternatingFiveExtension.PointCoreGeometry
open Subgroup AlternatingFiveFlag AlternatingFiveBorel
open scoped commutatorElement
local instance : DecidablePred (· ∈ B) := fun g => inferInstanceAs (Decidable (g.val 4 = 4))
local instance : Fintype B := Subtype.fintype _

instance vectors_normal : vectors.Normal := inferInstanceAs (MonoidHom.ker _).Normal

theorem vectors_le_outerCore : vectors ≤ outerCore := by
  intro x hx
  change x.right.val.val ∈ four
  change x.right = 1 at hx
  rw [hx]
  exact four.one_mem

theorem threeSpace_eq_map : threeSpace = three.map (SemidirectProduct.inl : V →* BorelModel) := by
  ext x
  constructor
  · rintro ⟨hx,hh⟩
    change x.right = 1 at hx
    refine ⟨x.left,hh,?_⟩
    exact SemidirectProduct.ext rfl hx.symm
  · rintro ⟨v,hv,rfl⟩
    exact ⟨rfl,hv⟩

theorem commutator_vectors_residual : ⁅vectors, pResidual 2 BorelModel⁆ = threeSpace := by
  apply le_antisymm
  · change _ ≤ vectors ⊓ residualModel
    rw [←residualModel_eq]
    exact le_inf (commutator_le_left _ _) (commutator_le_right _ _)
  · rw [threeSpace_eq_map,commutator_comm, map_le_iff_le_comap]
    apply three_le_of_differences
    intro g x
    have hg : (SemidirectProduct.inr g : BorelModel) ∈ pResidual 2 BorelModel := by
      rw [residualModel_eq]
      rfl
    have hc := commutator_mem_commutator hg
      (show (SemidirectProduct.inl (Multiplicative.ofAdd x) : BorelModel) ∈ vectors from rfl)
    change (SemidirectProduct.inl (Multiplicative.ofAdd (rho g.val.val x - x)) : BorelModel) ∈ ⁅pResidual 2 BorelModel, vectors⁆
    convert hc using 1
    rw [commutatorElement_def, ← map_inv, ← SemidirectProduct.inl_aut, ← map_inv, ← map_mul]
    congr 1
    exact congrArg Multiplicative.ofAdd (sub_eq_add_neg _ _)

private theorem four_commutators : ∀ b : B, b.val.val ∈ four →
    ∃ c : B, c.val.val ∈ four ∧ ⁅c,c₀⁆ = b := by decide +kernel

theorem commutator_outerCore_residual : ⁅outerCore, pResidual 2 BorelModel⁆ = coreModel := by
  apply le_antisymm
  · intro x hx
    have hR := commutator_le_left outerCore (pResidual 2 BorelModel) hx
    have hN := commutator_le_right outerCore (pResidual 2 BorelModel) hx
    rw [residualModel_eq] at hN
    exact ⟨hN,hR⟩
  · intro x hx
    rw [←SemidirectProduct.inl_left_mul_inr_right x]
    apply Subgroup.mul_mem
    · apply commutator_mono vectors_le_outerCore le_rfl
      rw [commutator_vectors_residual,threeSpace_eq_map]
      exact mem_map_of_mem _ hx.1
    · obtain ⟨c,hc,he⟩ := four_commutators x.right hx.2
      rw [←he, map_commutatorElement]
      apply commutator_mem_commutator
      · exact hc
      · rw [residualModel_eq]
        rfl
end BinaryPermutation.AlternatingFiveExtension.PointCoreGeometry
