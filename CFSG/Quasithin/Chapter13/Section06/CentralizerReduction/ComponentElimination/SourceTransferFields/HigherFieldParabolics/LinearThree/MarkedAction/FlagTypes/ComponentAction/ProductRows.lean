module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction.FlagTypes.ComponentAction.Restriction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction.FlagTypes.ComponentAction.ProductRows.Actions

/-!
# The nonquasisimple classifier rows at the actual SL₃ component

The two-factor source alternative gives a natural or doubled-natural action
on the literal quotient [V,C]/C_[V,C](C). The outer A₆–C₃ shape and the
hyperplane alternative are impossible when C is SL₃ over a field of order
2^m with m>1. This exhausts B.5.6(3–5) without an extra representation or
group-comparison premise. The proofs apply to every supplied moved section.

The source application restricts plusRepresentation to its actual offender
subgroup, identifies the original plus component there, and transports the
result back to plusComponentSection using the canonical quotient comparison.
The full classifier alternative is explicit here; its construction and the
independent quasisimple branch remain with the ComponentAction assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.6(3–5),
printed p.105; the paragraph before 13.6.14 and proof of 13.6.19, pp.929–931.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction.ComponentAction.ProductRows
open ChapterB.QuasisimpleSource ChapterB.SourceInduction

/-- The three nonquasisimple alternatives of the adequate B.5.6 classifier,
for an arbitrary construction of the original component's moved section. -/
theorem repeated_of_cases {D V F : Type*} [Group D] [Finite D]
    [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) D V}
    {C : Subgroup D} (hC : IsComponent D C) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hF : Nat.card F = 2 ^ m) (hm : 1 < m) (e : C ≃* SL(3,F))
    (s : MovedSection ρ C)
    (h : Nonempty (SourceTwoFactorCase ρ) ∨
      Nonempty (ChapterB.OuterSixThreeShape D) ∨ Nonempty (HyperplaneCase ρ)) :
    ∃ (E : BinaryField) (r : ℕ), 0 < r ∧
      IsRepeatedLinearNatural (s.action.comp C.subtype) E 3 r := by
  rcases h with h | h | h
  · obtain ⟨c⟩ := h
    exact twoFactor_repeated hC hF hm e s c
  · obtain ⟨c⟩ := h
    let := hC.2
    exact (not_outerSixThree hF hm e c).elim
  · obtain ⟨c⟩ := h
    exact (not_hyperplane hC hF hm e c).elim

open ComponentSelection
universe u
variable {G : Type u} [Group G] [Finite G]
variable (K L T : Subgroup G) (z v : G)
variable (hL : Tv T v ≤ normalizer (Lv L v : Set G))
variable (hz : Tv T v ≤ centralizer ({z} : Set G))
variable [IsElementaryAbelian 2 (Uv z v)]

/-- On the source offender restriction of plusRepresentation, all three
product/extension alternatives give the published canonical plus quotient.
The classifier alternative itself remains with the ComponentAction owner. -/
theorem plus_repeated_of_product_cases
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (hU : Uv z v ≤ (Gv v).pCoreIn 2)
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hcore : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    {F : Type*} [Field F] [Finite F] [CharP F 2] {m : ℕ}
    (hF : Nat.card F = 2 ^ m) (hm : 1 < m)
    (e : plusImage K L T z v hL hz K ≃* SL(3,F)) :
    letI : IsElementaryAbelian 2 (WK K L T z v) :=
      IsElementaryAbelian.of_le (WK_le_Uv K L T z v hK.1.1)
    let ρ := plusRepresentation K L T z v hL hz
    let I := offenderSubgroup ρ
    let C := plusImage K L T z v hL hz K
    (Nonempty (SourceTwoFactorCase (ρ.comp I.subtype)) ∨
      Nonempty (ChapterB.OuterSixThreeShape I) ∨
      Nonempty (HyperplaneCase (ρ.comp I.subtype))) →
    ∃ (E : BinaryField) (r : ℕ), 0 < r ∧
      IsRepeatedLinearNatural
        ((plusComponentSection K L T z v hL hz hK hn).action.comp C.subtype) E 3 r := by
  let : IsElementaryAbelian 2 (WK K L T z v) :=
    IsElementaryAbelian.of_le (WK_le_Uv K L T z v hK.1.1)
  intro ρ I C h
  have hCI : C ≤ I := plus_component_le_offender K L T z v hL hz hK hn hU hSyl
  let : C.Normal := plus_component_normal K L T z v hL hz hK hn
  let : IsQuasisimple C := plusImage_K_quasisimple K L T z v hL hz hK hcore
  have hcomp : IsComponent I (C.subgroupOf I) :=
    ⟨(inferInstance : (C.subgroupOf I).Normal).isSubnormal,
      IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hCI).symm⟩
  let s := plusComponentSection K L T z v hL hz hK hn
  let t := restrictSection s I hCI
  obtain ⟨E,r,hr,he⟩ := repeated_of_cases hcomp hF hm
    ((subgroupOfEquivOfLe hCI).trans e) t h
  exact ⟨E,r,hr,repeated_of_restrictedSection s I hCI t E 3 r he⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction.ComponentAction.ProductRows
