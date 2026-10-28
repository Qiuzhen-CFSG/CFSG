module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueSourceSingleFourMinus
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SmallRows.SingleA5FullCore

/-!
# Applying full-core recognition to original terminal solvability

The original normalized degree-four A₅ branch now has U=O₂(H). Its point
normalizer is the centralizer of an involution, with the actual minus
extraspecial core, returning conjugate, and A₅ or S₅ quotient. The A₅
case has exactly type J₂ or J₃. The selected
component, its T-conjugate span, and the literal embedded two-residual are
retained in the application below.

This is a conditional terminal-solvability consumer. The same owner must
still discharge the ambient A₅ recognition and Borel contradiction, including
the S₅ transfer case. The independently owned exact L₂(8) exclusion remains
explicit. The local I.4.7 entry is not global J₂/J₃ recognition.
Source: Aschbacher–Smith 14.2.16–17 and 14.3.6,15, pp.986–987,991,994.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

/-- The literal full core and involution centralizer supply the remaining
normalized-A₅ exclusion with its exact ambient recognition input. The independent
eight-row exclusion is retained on the same selected component. -/
theorem source_terminal_solvable_of_involution_centralizer_eight_exclusions
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
      F.U = K.pCoreIn 2 → F.U = F.H.pCoreIn 2 →
      F.E g = rankTwoSeed T M →
      (F.H = K ⊔ (T : Subgroup G) ∧
        (pResidual 2 F.H).map F.H.subtype = K ∧
        F.H ∈ Chapter3.HStar (T : Subgroup G) M ∧
        generalizedFitting F.H = pCore 2 F.H) →
      (∃ z : G, orderOf z = 2 ∧ F.H = centralizer ({z} : Set G) ∧
        Janko23.ambientCore z = F.U ∧
        Nonempty (Janko23.localCore z ≃* MinusExtraspecial.Model) ∧
        (∃ t ∈ F.U, IsConj z t ∧ t ≠ z) ∧
        ((Janko23.HTypeAt z ∧ (Janko23.J2Type G ∨ Janko23.J3Type G)) ∨ Nonempty
          ((Janko23.involutionCentralizer z ⧸ Janko23.localCore z) ≃* Equiv.Perm (Fin 5)))) →
      False)
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
    have hcore := source_single_a5_component_core_of_four hG T hempty hM hu hmany
      hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
    have hpar := source_single_a5_full_parabolic_of_four hG T hempty hM hu hmany
      hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
    obtain ⟨hfull,hlocal⟩ := source_single_a5_involution_centralizer_of_four hG T hempty hM hu hmany
      hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
    exact hfour hhat K hK hspan e5 hcore hfull hint hpar hlocal
  · exact height K hK h8

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
