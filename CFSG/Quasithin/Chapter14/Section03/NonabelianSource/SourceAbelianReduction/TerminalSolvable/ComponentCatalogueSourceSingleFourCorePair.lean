module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueSourceSingleFourMinus
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SmallRows.SingleA5ComponentCore

/-!
# Applying the two-core pair calculation to terminal solvability

The original selected component has the commutator-generated closure
as its exact two-core, and the actual point normalizer is KT with
embedded two-residual K. The actual opposite residual has order 192 and the
same order-64 two-core as I₂, with a fixed-point-free cubic. The core-pair
and centralizing-supplement calculations discharge these local premises
in the remaining normalized-A₅ exclusion.

This is a conditional consumer. The terminal-solvability owner still has
to eliminate the centralizing supplement, recognize the ambient field-four
case and obtain its Borel contradiction. The independent L₂(8) exclusion
retains its original exact contract. No full-core equality or ambient
recognition is assumed as a proved source theorem here.

Source: Aschbacher–Smith 14.2.16–17 and 14.3.6,15, pp.986–987,991,994.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

/-- Discharge the original A₅ local core premises and apply its remaining
ambient exclusion, alongside the independently owned exact eight-row exclusion. -/
theorem source_terminal_solvable_of_core_pair_eight_exclusions
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
      Nonempty (F.U ≃* MinusExtraspecial.Model) → F.E g = rankTwoSeed T M →
      F.U = ⁅F.U,K⁆ → F.U ≤ K.pCoreIn 2 →
      (F.I₂ (sourceResidual M Mc)).pCoreIn 2 ⊓ F.H.pCoreIn 2 = F.W →
      (sourceResidual M Mc).pCoreIn 2 = (F.I₂ (sourceResidual M Mc)).pCoreIn 2 →
      Nat.card (sourceResidual M Mc) = 192 →
      (∃ c : G, c ∈ sourceResidual M Mc ∧ orderOf c = 3 ∧
        (F.I₂ (sourceResidual M Mc)).pCoreIn 2 ⊓ centralizer ({c} : Set G) = ⊥) →
      (let D := F.H.pCoreIn 2 ⊓ centralizer (F.U : Set G)
       F.U ⊔ D = F.H.pCoreIn 2 ∧ F.U ⊓ D = F.Vi 1 ∧
        F.H ≤ normalizer (D : Set G) ∧
        ⁅D,(F.I₂ (sourceResidual M Mc)).pCoreIn 2⁆ ≤ F.Vi 1 ∧
        (F.U = F.H.pCoreIn 2 ↔ D = F.Vi 1)) → False)
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
      norm_num [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hd]
    obtain ⟨hcomm,hUK⟩ := source_single_a5_closure_component_of_four hG T hempty hM hu hmany
      hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
    obtain ⟨_,_,hRQ,_⟩ := source_single_a5_core_pair_of_four hG T hempty hM hu hmany
      hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
    obtain ⟨_,_,hYR,hY,hc⟩ := source_single_a5_opposite_residual_of_four hG T hempty hM hu hmany
      hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
    exact hfour hhat K hK hspan e5 hminus hint hcomm hUK hRQ hYR hY hc
      (source_single_a5_core_supplement_of_four hG T hempty hM hu hmany
        hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd)
  · exact height K hK h8

/-- Identify the selected component core and apply the remaining A₅
ambient exclusion, alongside the independently owned exact eight-row exclusion. -/
theorem source_terminal_solvable_of_component_core_eight_exclusions
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
      Nonempty (F.U ≃* MinusExtraspecial.Model) → F.E g = rankTwoSeed T M →
      F.U = ⁅F.U,K⁆ → F.U = K.pCoreIn 2 →
      (F.H = K ⊔ (T : Subgroup G) ∧
        (pResidual 2 F.H).map F.H.subtype = K ∧
        F.H ∈ Chapter3.HStar (T : Subgroup G) M ∧
        generalizedFitting F.H = pCore 2 F.H) →
      (F.I₂ (sourceResidual M Mc)).pCoreIn 2 ⊓ F.H.pCoreIn 2 = F.W →
      (sourceResidual M Mc).pCoreIn 2 = (F.I₂ (sourceResidual M Mc)).pCoreIn 2 →
      Nat.card (sourceResidual M Mc) = 192 →
      (∃ c : G, c ∈ sourceResidual M Mc ∧ orderOf c = 3 ∧
        (F.I₂ (sourceResidual M Mc)).pCoreIn 2 ⊓ centralizer ({c} : Set G) = ⊥) →
      (let D := F.H.pCoreIn 2 ⊓ centralizer (F.U : Set G)
       F.U ⊔ D = F.H.pCoreIn 2 ∧ F.U ⊓ D = F.Vi 1 ∧
        F.H ≤ normalizer (D : Set G) ∧
        ⁅D,(F.I₂ (sourceResidual M Mc)).pCoreIn 2⁆ ≤ F.Vi 1 ∧
        (F.U = F.H.pCoreIn 2 ↔ D = F.Vi 1)) → False)
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
      norm_num [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hd]
    obtain ⟨hcomm,hUK⟩ := source_single_a5_closure_component_of_four hG T hempty hM hu hmany
      hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
    obtain ⟨_,_,hRQ,_⟩ := source_single_a5_core_pair_of_four hG T hempty hM hu hmany
      hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
    obtain ⟨_,_,hYR,hY,hc⟩ := source_single_a5_opposite_residual_of_four hG T hempty hM hu hmany
      hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
    have hcore := source_single_a5_component_core_of_four hG T hempty hM hu hmany
      hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
    have hpar := source_single_a5_full_parabolic_of_four hG T hempty hM hu hmany
      hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
    exact hfour hhat K hK hspan e5 hminus hint hcomm hcore hpar hRQ hYR hY hc
      (source_single_a5_core_supplement_of_four hG T hempty hM hu hmany
        hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd)
  · exact height K hK h8


end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
