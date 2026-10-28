module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SmallRows.ExchangedA5Action
public import Theory.Representation.OrthogonalFourPlusMatrix.SymplecticNormalizerBounds

/-!
# The order contradiction for the exchanged A₅ branch

The natural determinant module embeds the faithful terminal action in its
symplectic normalizer. Original 14.3.12 identifies the terminal kernel with
O₂(H), so the actual quotient of ⟨Kᵀ,T⟩ has order at most that normalizer.
The full S₅ wreath C₂ has order 28800, contradicting the required normalizer
bound 14400. The same kernel identifies ⟨Kᵀ⟩/O₂(⟨Kᵀ⟩) with the model,
providing the literal quotient needed by the local Borel argument.

The intrinsic symplectic normalizer estimates are proved and discharged in
the final two source consumers. The tensor action and outside-actor clause
of G.11.2(7), and the actual wreath quotient forced by 14.3.6(3), remain
explicit. The original terminal-solvability assembly owns their discharge;
this does not yet prove the complete 14.3.15 exclusion.
Source: Aschbacher--Smith, printed pp.364--367,991--994.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ClassicalOrthogonal.FourPlusMatrix.Binary
open Theory.SpecificGroups.Alternating.FiveSquareAutomorphisms

theorem ExchangedA5.wreath_card : Nat.card Wreath = 28800 := by
  rw [RegularWreathProduct.card]
  norm_num [Theory.SpecificGroups.Alternating.FiveSquareAutomorphisms.Sym,
    Nat.card_perm, Nat.card_fin, WreathTwoElementaryRank.C2,
    Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {V : Subgroup G} {F : InvariantFlag T V 2}
  [IsElementaryAbelian 2 F.Uhat] {g : G} {K : Subgroup G}

/-- A concrete wreath quotient contradicts the actual symplectic normalizer
bound; no isomorphism of an unrelated group is used. -/
theorem ExchangedA5.ActionModel.false_of_kernel_and_wreath
    (m : ExchangedA5.ActionModel F K) (hK : ComponentLift F g K)
    (hk : F.terminalHatAction.ker = pCore 2 F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (hB : ∀ h u v, B (F.terminalRepresentation h u) (F.terminalRepresentation h v) = B u v)
    (hbound : Nat.card (symplecticNormalizer (m.form B)) ≤ 14400)
    (eJ : ((conjugateSpanBy K (T : Subgroup G) ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (conjugateSpanBy K (T : Subgroup G) ⊔ (T : Subgroup G) : Subgroup G)) ≃* Wreath) : False := by
  have hle := (m.span_join_core_quotient_card_le hK hk B hB).trans hbound
  rw [Nat.card_congr eJ.toEquiv, ExchangedA5.wreath_card] at hle
  omega

section Source
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
  (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
  {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
  (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  (hcard : Nat.card (localModule T M) = 4)
  (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
  (F : InvariantFlag T (rankTwoSeed T M) 2)
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  (hne : ¬ IsMulCommutative F.U) (g : G)
  [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
    (hatSpace F (F.E g)) (F.terminalDot (F.X g))
    ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
  (hm : Module.finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) ≤
    Module.finrank (ZMod 2) (Additive F.Uhat) / 2 - 1)
  {K : Subgroup G} (hK : ComponentLift F g K) (m : ExchangedA5.ActionModel F K)

include hG hempty hM hu hmany hcard e hne hgP hgH hyp hm hK m in
/-- The original small-actor geometry supplies the kernel; the normal span
then has the precise intrinsic quotient required by 14.3.6(3). -/
theorem source_exchanged_a5_span_quotient_of_small_actor :
    Nonempty ((conjugateSpanBy K (T : Subgroup G) ⧸
      pCore 2 (conjugateSpanBy K (T : Subgroup G))) ≃* ExchangedA5.ModelGroup) := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  let d := Recognition.rankTwo_closure_geometry h F hne
  have hk := (Recognition.rankTwo_small_actor_geometry h F g d hne hgP hgH hyp hm).2.2.2.2
  exact ⟨(hK.spanCoreQuotientEquiv F hk).trans m.componentEquiv⟩

include hG hempty hM hu hmany hcard e hne hgP hgH hyp hm hK m in
/-- Source consumer with the three remaining independent inputs displayed.
The normalizer bound is on the transported original form. -/
theorem source_exchanged_a5_false_of_small_actor_and_wreath
    (hbound : Nat.card (symplecticNormalizer (m.form B)) ≤ 14400)
    (eJ : ((conjugateSpanBy K (T : Subgroup G) ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (conjugateSpanBy K (T : Subgroup G) ⊔ (T : Subgroup G) : Subgroup G)) ≃* Wreath) : False := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  let d := Recognition.rankTwo_closure_geometry h F hne
  have hk := (Recognition.rankTwo_small_actor_geometry h F g d hne hgP hgH hyp hm).2.2.2.2
  exact m.false_of_kernel_and_wreath hK hk B hyp.preserves hbound eJ

include hG hempty hM hu hmany hcard e hne hgP hgH hyp hK m in
/-- G.11.2(7)'s outside clause and the concrete elementary normalizer bound
discharge the small-actor premise, so the entire kernel comparison is internal. -/
theorem source_exchanged_a5_false_of_model_and_wreath
    (hout : ¬ F.terminalDot (F.X g) ≤ F.terminalDot (conjugateSpanBy K (T : Subgroup G)))
    (hactors : ∀ A : Subgroup (symplecticNormalizer (m.form B)), IsElementaryAbelian 2 A →
      ¬ A.map (symplecticNormalizer (m.form B)).subtype ≤ linearAction.range → Nat.card A ≤ 8)
    (hbound : Nat.card (symplecticNormalizer (m.form B)) ≤ 14400)
    (eJ : ((conjugateSpanBy K (T : Subgroup G) ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (conjugateSpanBy K (T : Subgroup G) ⊔ (T : Subgroup G) : Subgroup G)) ≃* Wreath) : False := by
  have hm' := m.small_actor_bound hK B hyp.preserves hactors (F.terminalDot (F.X g)) hout
  exact source_exchanged_a5_false_of_small_actor_and_wreath hG T hempty hM hu hmany hcard e
    F hne g hgP hgH hyp hm' hK m hbound eJ

include hG hempty hM hu hmany hcard e hne hgP hgH hyp hK m in
/-- Supply the literal quotient input to the independent local wreath proof
from the model and its elementary normalizer bound. -/
theorem source_exchanged_a5_span_quotient_of_model
    (hout : ¬ F.terminalDot (F.X g) ≤ F.terminalDot (conjugateSpanBy K (T : Subgroup G)))
    (hactors : ∀ A : Subgroup (symplecticNormalizer (m.form B)), IsElementaryAbelian 2 A →
      ¬ A.map (symplecticNormalizer (m.form B)).subtype ≤ linearAction.range → Nat.card A ≤ 8) :
    Nonempty ((conjugateSpanBy K (T : Subgroup G) ⧸
      pCore 2 (conjugateSpanBy K (T : Subgroup G))) ≃* ExchangedA5.ModelGroup) := by
  have hm' := m.small_actor_bound hK B hyp.preserves hactors (F.terminalDot (F.X g)) hout
  exact source_exchanged_a5_span_quotient_of_small_actor hG T hempty hM hu hmany hcard e
    F hne g hgP hgH hyp hm' hK m

include hG hempty hM hu hmany hcard e hne hgP hgH hyp hK m in
/-- The intrinsic tensor estimates discharge both numerical normalizer
premises in the original exchanged-component contradiction. The remaining
inputs are the actual tensor action, its outside actor and the local wreath
quotient from 14.3.6(3), all retained by the terminal-solvability assembly. -/
theorem source_exchanged_a5_false_of_tensor_and_wreath
    (hout : ¬ F.terminalDot (F.X g) ≤ F.terminalDot (conjugateSpanBy K (T : Subgroup G)))
    (eJ : ((conjugateSpanBy K (T : Subgroup G) ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (conjugateSpanBy K (T : Subgroup G) ⊔ (T : Subgroup G) : Subgroup G)) ≃* Wreath) : False := by
  exact source_exchanged_a5_false_of_model_and_wreath hG T hempty hM hu hmany hcard e
    F hne g hgP hgH hyp hK m hout
    (symplecticNormalizer_outer_elementary_card_le (m.form B))
    (symplecticNormalizer_card_le (m.form B) (m.form_nondegenerate hyp.nondegenerate)
      (m.form_invariant B hyp.preserves)) eJ

include hG hempty hM hu hmany hcard e hne hgP hgH hyp hK m in
/-- The tensor action and original outside actor supply the literal normal-span
quotient, with no numerical normalizer estimate left as a premise. -/
theorem source_exchanged_a5_span_quotient_of_tensor
    (hout : ¬ F.terminalDot (F.X g) ≤ F.terminalDot (conjugateSpanBy K (T : Subgroup G))) :
    Nonempty ((conjugateSpanBy K (T : Subgroup G) ⧸
      pCore 2 (conjugateSpanBy K (T : Subgroup G))) ≃* ExchangedA5.ModelGroup) := by
  exact source_exchanged_a5_span_quotient_of_model hG T hempty hM hu hmany hcard e
    F hne g hgP hgH hyp hK m hout
    (symplecticNormalizer_outer_elementary_card_le (m.form B))

end Source
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
