module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.DualOffender.Faithfulness
public import Theory.Representation.BinaryOffender.AlternatingSevenIrrPlus

/-!
# Original moved-action displacement in the source block

The range of one operator on I=[V,⟨K^G⟩] embeds into the literal subgroup
U containing [V,K]. Its order therefore bounds the fixed codimension of
the actual K actor in the centralizer quotient. No model or quotient-kernel
identification enters this comparison.
Source: Aschbacher–Smith C.5.13, printed p.163.
-/
public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.DualOffender
variable {G : Type*} [Group G] [Finite G]

/-- The original K-actor on I has displacement at most the binary rank
of the actual subgroup containing [V,K]. -/
theorem moved_displacement_le_card (V K U : Subgroup G)
    [V.Normal] [IsElementaryAbelian 2 V] (hcomm : ⁅V,K⁆ ≤ U)
    (k : G) (hk : k ∈ K) :
    let a : closureImage V K := ⟨QuotientGroup.mk' (centralizer (V : Set G)) k,
      mem_map_of_mem _ (le_normalClosure hk)⟩
    fixedCodim (movedRepresentation V K) (zpowers a) ≤ Nat.log 2 (Nat.card U) := by
  let a : closureImage V K := ⟨QuotientGroup.mk' (centralizer (V : Set G)) k,
    mem_map_of_mem _ (le_normalClosure hk)⟩
  let ρ := movedRepresentation V K
  let W := LinearMap.range (ρ a - LinearMap.id)
  have hd (w : W) : (w.val.val.toMul : G) ∈ U := by
    obtain ⟨v,hv⟩ := w.property
    rw [← hv]
    change (((centralizerQuotient V (QuotientGroup.mk' (centralizer (V : Set G)) k)
      v.val - v.val).toMul : G)) ∈ U
    rw [toMul_sub,Subgroup.coe_div,centralizerQuotient_apply,div_eq_mul_inv]
    apply hcomm
    rw [commutator_comm]
    exact commutator_mem_commutator hk v.val.toMul.property
  have hc : Nat.card W ≤ Nat.card U :=
    Nat.card_le_card_of_injective (fun w : W => (⟨w.val.val.toMul,hd w⟩ : U)) (by
      intro b c he
      apply Subtype.ext
      apply Subtype.ext
      apply Additive.toMul.injective
      exact Subtype.ext (congrArg (fun u : U => (u : G)) he))
  have hh := Nat.log_monotone (b := 2) hc
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
    Nat.log_pow (by decide : 1 < 2)] at hh
  change fixedCodim ρ (zpowers a) ≤ Nat.log 2 (Nat.card U)
  rw [fixedCodim_zpowers_eq_displacement_rank]
  exact hh
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.DualOffender
