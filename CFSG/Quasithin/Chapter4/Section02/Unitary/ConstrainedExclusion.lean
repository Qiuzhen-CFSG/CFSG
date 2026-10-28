module
public import CFSG.Quasithin.Chapter4.Section02.Unitary.FiniteExclusions
public import CFSG.Quasithin.Chapter4.Section02.Unitary.RankTwoExclusions
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedLinearThreeOddRank
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedLinearTwo

/-!
# No constrained escaping component for the normal unitary residual

The original normal residual retains three-rank two in its nontrivial
component action. The binary linear-three parabolic has odd rank at most
one; its field-two case is excluded by order. Together with the completed
rank-one, rank-two and finite-row exclusions, this eliminates every
constrained star model supplied by the genuine C.2.7 source. The escaping
C-component is therefore an ordinary component.

The seed, radical, relative normality and core-central action remain
literal throughout. This removes the constrained branch of the original
4.2.12/C.4.8 inspection; ordinary component recognition remains separate.
Source: Aschbacher–Smith C.2.7 and C.4.5–8, pp.145–147,152–154,
and 4.2.12–13, pp.610–612.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC.HypothesisC28
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {H M L R V : Subgroup G}
local notation "D" => commutator (Atlas.G2.Model (ZMod 2))

theorem no_unitary_constrained_linear_three
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (hn : (L.subgroupOf M).Normal) (a : L ⧸ pCore 2 L ≃* D)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K)
    (F : BinaryField)
    (e : starImage (K.map H.subtype) R (K.map H.subtype) ≃* SL(3,F.Carrier)) : False := by
  by_cases hF : 1 < F.degree
  · have hcard : 4 ≤ Nat.card F.Carrier := by
      rw [F.card_eq]
      exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 2 ≤ F.degree)
    have hl := h.unitary_constrained_action_threeRank hn a K hK hq hout
    have hu := h.constrained_linear_three_span_oddRank_le_one K hK hq hout hfK
      e hcard (by decide : Odd 3)
    omega
  · have hd : F.degree = 1 := by have hp := F.degree_pos; omega
    have hc := h.unitary_component_central_order_dvd a K hK hq hout
    rw [Nat.card_congr (h.constrained_linear_three_simple_equiv K hK hq hout hfK e).toEquiv,
      Matrix.PSL3.LinearThree.card_projective F.Carrier,F.card_eq,hd] at hc
    norm_num at hc

/-- Every constrained star-model row is impossible for the actual normal
unitary residual; the C.2.7 model marking is constructed from the source. -/
theorem no_unitary_constrained_component
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (hn : (L.subgroupOf M).Normal) (a : L ⧸ pCore 2 L ≃* D)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K) : False := by
  have hm := C27Source.star_model_from_source (h.constrained_source_input K hK hq hout hfK)
  cases hm with
  | linearTwo F e => exact h.no_constrained_component_star_linear_two K hK hq hout hfK F e
  | linearThree F e => exact h.no_unitary_constrained_linear_three hn a K hK hq hout hfK F e
  | symplectic F hF e =>
    apply h.no_unitary_constrained_sp4 hn a K hK hq hout hfK e
    rw [F.card_eq]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 2 ≤ F.degree)
  | g2 F hF e =>
    apply h.no_unitary_constrained_g2 hn a K hK hq hout hfK e
    rw [F.card_eq]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 2 ≤ F.degree)
  | g2DerivedTwo e => exact h.no_unitary_constrained_g2_derived_two a K hK hq hout hfK e
  | alternating n hd e =>
    apply h.no_unitary_constrained_alternating a K hK hq hout hfK (n := n) ?_ ?_ e
    · rcases hd with rfl | rfl | rfl | rfl <;> omega
    · rcases hd with rfl | rfl | rfl | rfl <;> omega
  | linearFiveTwo e => exact h.no_unitary_constrained_linear_five_two a K hK hq hout hfK e
  | tripleSix _ e => exact h.no_unitary_constrained_triple_six a K hK hq hout hfK e

/-- An escaping C-component for this original residual is ordinary. -/
theorem unitary_escaping_component_isComponent
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (hn : (L.subgroupOf M).Normal) (a : L ⧸ pCore 2 L ≃* D)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) : IsComponent H K := by
  exact (hK.component_or_generalizedFitting_eq_pCore h.oddCore_eq_bot).resolve_right
    (h.no_unitary_constrained_component hn a K hK hq hout)

end CFSG.Quasithin.ChapterC.HypothesisC28
