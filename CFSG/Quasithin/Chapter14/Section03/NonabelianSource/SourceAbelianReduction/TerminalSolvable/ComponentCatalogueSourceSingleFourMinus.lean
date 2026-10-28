module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueSourceSingleFourCenter
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SmallRows.SingleA5Minus

/-!
# The terminal catalogue with the literal minus closure and opposite local

The normalized A₅ alternative now carries an actual Q₈ * D₈ equivalence,
the seed and two-core intersections with the prescribed conjugate, and
the order-384 opposite local group. All are derived from the original source
prefix on the same selected K and its T-conjugate span.

The consumer discharges these premises of the remaining ambient exclusion.
The full two-core identification and ambient A₅ exclusion stay with terminal
solvability; the exact L₂(8) row stays with its independent exclusion owner.
This conditional assembly does not establish original 14.3.15 solvability.

Source: Aschbacher–Smith 14.3.6 and 14.3.13–15, pp.991,993–994.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

section Source
variable {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (g : G)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
include hG hempty hM hu hmany hcard e hnot hne hgP hgH hyp

/-- The original catalogue supplies the concrete minus closure, exact intersections
and opposite local orders, or the independently owned eight row. -/
theorem source_normalized_a5_minus_or_eight
    (hn : ¬ Group.IsSolvable F.TerminalHdot) :
    ∃ K : Subgroup G, ComponentLift F g K ∧
      ((K = conjugateSpanBy K (T : Subgroup G) ∧
        Nonempty (F.terminalDot K ≃* alternatingGroup (Fin 5)) ∧
        finrank (ZMod 2) (Additive F.Uhat) = 4 ∧
        F.ZU = F.Vi 1 ∧ IsExtraspecial 2 F.U ∧ Nat.card F.U = 32 ∧
        F.terminalHatAction.ker = pCore 2 F.H ∧
        Nonempty (F.U ≃* MinusExtraspecial.Model) ∧ F.E g = rankTwoSeed T M ∧
        F.H.pCoreIn 2 ⊓ conjugate F.U g = rankTwoSeed T M ∧
        Nat.card F.W = 16 ∧ Nat.card ((F.I₂ (sourceResidual M Mc)).pCoreIn 2) = 64 ∧
        Nat.card (F.I₂ (sourceResidual M Mc)) = 384) ∨ EightImageRow F K) := by
  obtain ⟨K,hK,⟨hspan,⟨e5⟩,hd⟩ | h8⟩ := source_normalized_a5_four_or_eight
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hyp hn
  · obtain ⟨hZ,hE,hU,hker⟩ := source_single_a5_extraspecial_of_four
      hG T hempty hM hu hmany hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
    exact ⟨K,hK,Or.inl ⟨hspan,⟨e5⟩,hd,hZ,hE,hU,hker,
      source_single_a5_minus_model_of_four hG T hempty hM hu hmany hcard e
        F hne hnot g hgP hgH hyp hK e5 hspan hd,
      source_single_a5_intersection_eq_seed_of_four hG T hempty hM hu hmany hcard e
        F hne hnot g hgP hgH hyp hK e5 hspan hd,
      source_single_a5_core_intersection_of_four hG T hempty hM hu hmany hcard e
        F hne hnot g hgP hgH hyp hK e5 hspan hd,
      source_single_a5_opposite_orders_of_four hG T hempty hM hu hmany hcard e
        F hne hnot g hgP hgH hyp hK e5 hspan hd⟩⟩
  · exact ⟨K,hK,Or.inr h8⟩

end Source
/-- Apply an ambient exclusion for the marked minus degree-four branch and
the exact independently owned L₂(8) exclusion to original terminal solvability.
The terminal-solvability owner retains both remaining exclusions. -/
theorem source_terminal_solvable_of_minus_eight_exclusions
    {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hfour : Nat.card F.Uhat = 16 → ∀ K : Subgroup G, ComponentLift F g K →
      K = conjugateSpanBy K (T : Subgroup G) →
      (F.terminalDot K ≃* alternatingGroup (Fin 5)) →
      F.ZU = F.Vi 1 → IsExtraspecial 2 F.U → Nat.card F.U = 32 →
      F.terminalHatAction.ker = pCore 2 F.H →
      Nonempty (F.U ≃* MinusExtraspecial.Model) → F.E g = rankTwoSeed T M →
      F.H.pCoreIn 2 ⊓ conjugate F.U g = rankTwoSeed T M →
      Nat.card F.W = 16 → Nat.card ((F.I₂ (sourceResidual M Mc)).pCoreIn 2) = 64 →
      Nat.card (F.I₂ (sourceResidual M Mc)) = 384 → False)
    (height : ∀ K : Subgroup G, ComponentLift F g K → EightImageRow F K → False) :
    Group.IsSolvable F.TerminalHdot := by
  by_contra hn
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  let := rankTwoSeed_elementary h
  obtain ⟨_,he,hx,B,v,hyp,_⟩ := Recognition.rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := he
  let := hx
  obtain ⟨K,hK,⟨hspan,⟨e5⟩,hd,hZ,hE,hU,hker,hminus,hint,hcint,hW,hR,hI⟩ | h8⟩ :=
    source_normalized_a5_minus_or_eight hG T hempty hM hu hmany hcard e
      hnot F hne g hgP hgH hyp hn
  · have hhat : Nat.card F.Uhat = 16 := by
      change Nat.card (Additive F.Uhat) = 16
      norm_num [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,hd]
    exact hfour hhat K hK hspan e5 hZ hE hU hker hminus hint hcint hW hR hI
  · exact height K hK h8

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
