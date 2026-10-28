module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueSourceSingleFourMinus
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SmallRows.SingleA5OutsideCentralizer

/-!
# The ambient outside-involution centralizer in the terminal consumer

The actual S₅ branch now supplies C_T(j) Sylow in C_G(j), its order at
most 32, and nonfusion of j with every involution of the same core U.
The characteristic square argument uses the literal point involution and
preserves K and its T-conjugate span. The source consumer passes these facts
to the remaining outside-core separation and J₂/J₃ recognition argument.

Those remaining ambient exclusions belong to the terminal-solvability owner;
the exact L₂(8) exclusion remains explicit for its independent producer.
Source: Aschbacher–Smith 14.2.17(1) and 14.3.15, printed pp.987 and 994.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

/-- Apply global outside-centralizer control to the original terminal
solvability reduction. Outside-core separation and ambient recognition remain
with this assembly owner; the exact eight-row exclusion remains explicit. -/
theorem source_terminal_solvable_of_global_outside_centralizer_eight_exclusions
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
      (Nat.card K = 1920 ∧
        ((K.subgroupOf F.H).index = 1 ∨ (K.subgroupOf F.H).index = 2) ∧
        ((K.subgroupOf (T : Subgroup G)).index = 1 ∨
          (K.subgroupOf (T : Subgroup G)).index = 2)) →
      (∀ x : G, orderOf x = 2 → ∃ y : K, orderOf y = 2 ∧ IsConj x (y:G)) →
      (∃ z : G, orderOf z = 2 ∧ F.H = centralizer ({z} : Set G) ∧
        (∀ u ∈ F.U, orderOf u = 2 → IsConj z u) ∧
        (∀ u v : K, orderOf u = 2 → orderOf v = 2 →
          (u:G) ∉ F.U → (v:G) ∉ F.U → IsConj u v) ∧
        (∀ u : K, orderOf u = 2 → (u:G) ∉ F.U →
          Nat.card (centralizer ({u} : Set K)) = 16)) →
      (Janko23.OneInvolutionClass G ∨ Janko23.TwoInvolutionClasses G) →
      (Nonempty (F.TerminalHdot ≃* Equiv.Perm (Fin 5)) →
        Nat.card T = 256 ∧
        ∃ z j : G, orderOf z = 2 ∧ F.H = centralizer ({z} : Set G) ∧
          j ∈ (T : Subgroup G) ∧ j ∉ K ∧ orderOf j = 2 ∧
          Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({j} : Set G))
            (centralizer ({j} : Set G)) ∧
          Nat.card ↥((T : Subgroup G) ⊓ centralizer ({j} : Set G)) ≤ 32 ∧
          (∀ x ∈ (T : Subgroup G) ⊓ centralizer ({j} : Set G), orderOf x = 4 → x^2=z) ∧
          (∀ u ∈ F.U, orderOf u = 2 → ¬ IsConj j u)) →
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
      (source_single_a5_component_index_of_four hG T hempty hM hu hmany hcard e
        F hne hnot g hgP hgH hyp hK e5 hspan hd)
      (source_single_a5_involutions_into_component_of_four hG T hempty hM hu hmany hcard e
        F hne hnot g hgP hgH hyp hK e5 hspan hd)
      (source_single_a5_component_involution_fusion_of_four hG T hempty hM hu hmany hcard e
        F hne hnot g hgP hgH hyp hK e5 hspan hd)
      (source_single_a5_involution_classes_of_four hG T hempty hM hu hmany hcard e
        F hne hnot g hgP hgH hyp hK e5 hspan hd)
      (fun ⟨eS⟩ => source_single_a5_outside_centralizer_sylow_of_symmetric_five
        hG T hempty hM hu hmany hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd eS)
  · exact height K hK h8

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
