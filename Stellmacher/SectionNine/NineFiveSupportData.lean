module

public import Stellmacher.SectionNine.NineFiveTransvectionInputs
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Two-conjugate support data and the cardinality calculation for (9.5)

The record describes the lifted four-element support and its conjugate
in the terminal module, as used on printed pp.52–53 of
`refs/files/stellmacher-n-group.pdf`. No existence assertion is made here.
The support producer must supply every field from the original ambient
Section Nine hypotheses, including the intersection in the large case.

Given that data, elementary abelianness and the product cardinality formula
give orders eight and thirty-two. This calculation does not identify the
terminal core quotient and is not the numbered (9.5) theorem.
-/

open scoped IsMulCommutative

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext

universe u

public structure NineFiveSupportData
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (prev : ctx.Γ.Vertex) (actor : G) where
  support : Subgroup G
  conjugator : G
  center_card : Nat.card (ZAt ctx.Γ ctx.criticalPath.a') = 2
  center_le : ZAt ctx.Γ ctx.criticalPath.a' ≤ support
  support_index : QuotientCardEq support (ZAt ctx.Γ ctx.criticalPath.a') 4
  commutator_le : ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ≤ support
  residual_normalizes : EAt ctx.Γ ctx.criticalPath.a' ≤
    Subgroup.normalizer (support : Set G)
  conjugator_mem : conjugator ∈ twoCoreIn (EAt ctx.Γ
    (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
      Nat.lt_succ_of_le (Nat.sub_le _ _)⟩))
  span : VAt ctx.Γ ctx.criticalPath.a' =
    support ⊔ support.map (MulAut.conj conjugator⁻¹).toMonoidHom
  support_intersection : support ≠ support.map (MulAut.conj conjugator⁻¹).toMonoidHom →
    support ⊓ support.map (MulAut.conj conjugator⁻¹).toMonoidHom =
      ZAt ctx.Γ ctx.criticalPath.a'
  neighbor_intersection : support ≠ support.map (MulAut.conj conjugator⁻¹).toMonoidHom →
    Nat.card (VAt ctx.Γ ctx.criticalPath.a' ⊓ VAt ctx.Γ prev : Subgroup G) = 2 ^ 3

public theorem nine_five_cardinalities_of_support
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hb : 1 < ctx.criticalPath.length)
    (prev : ctx.Γ.Vertex) (actor : G)
    (data : NineFiveSupportData ctx prev actor) :
    Nat.card (VAt ctx.Γ ctx.criticalPath.a') = 2 ^ 3 ∨
      (Nat.card (VAt ctx.Γ ctx.criticalPath.a') = 2 ^ 5 ∧
        Nat.card (VAt ctx.Γ ctx.criticalPath.a' ⊓ VAt ctx.Γ prev : Subgroup G) = 2 ^ 3) := by
  have hsupport : Nat.card data.support = 8 := by
    have hindex := data.support_index
    unfold QuotientCardEq at hindex
    simpa [data.center_card] using hindex
  by_cases hequal : data.support = data.support.map
      (MulAut.conj data.conjugator⁻¹).toMonoidHom
  · left
    rw [data.span, ← hequal, sup_idem, hsupport]
    norm_num
  · right
    refine ⟨?_, data.neighbor_intersection hequal⟩
    let _ : IsElementaryAbelian 2 (VAt ctx.Γ ctx.criticalPath.a') :=
      (nine_three_second_extraction_inputs ctx hb).2.2.1
    let other := data.support.map (MulAut.conj data.conjugator⁻¹).toMonoidHom
    have hfirst : data.support ≤ VAt ctx.Γ ctx.criticalPath.a' :=
      le_sup_left.trans_eq data.span.symm
    have hother : other ≤ VAt ctx.Γ ctx.criticalPath.a' :=
      le_sup_right.trans_eq data.span.symm
    have hcentral : other ≤ Subgroup.centralizer (data.support : Set G) := by
      intro element helement
      rw [Subgroup.mem_centralizer_iff]
      intro point hpoint
      exact congrArg Subtype.val (mul_comm
        (⟨point, hfirst hpoint⟩ : VAt ctx.Γ ctx.criticalPath.a')
        (⟨element, hother helement⟩ : VAt ctx.Γ ctx.criticalPath.a'))
    have hnormal := hcentral.trans (Subgroup.centralizer_le_normalizer _)
    have hproduct := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes
      data.support other hnormal
    have hotherCard : Nat.card other = 8 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj data.conjugator⁻¹).injective]
      exact hsupport
    rw [hsupport, hotherCard, data.support_intersection hequal,
      data.center_card, ← data.span] at hproduct
    norm_num at hproduct ⊢
    omega

end Stellmacher.SectionNine
