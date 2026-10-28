module

public import CFSG.Quasithin.ChapterA.Section03.Basic
public import Theory.GroupAction.FullyMovedIrreducibleCore
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.Core
public import Theory.Quasithin.EvenCharacteristic

/-!
# Original-section exclusion in the first J₄ involution centralizer

The first involution centralizer has a self-centralizing extraspecial two-core.
A full Sylow normalizes the local C-component B and the original chosen
fully moved elementary subgroup E. If O₂(B) fixes E and E/C_E(B) is
irreducible, the commuting fixed-point lemma places E in the center of the
ambient core, of order two. Thus it cannot have order at least sixteen.

This uses the actual chosen section, not irreducibility of the whole block
layer. The invariant-subgroup hypothesis is the literal section irreducibility
contract, supplied by BinaryConjugationSection.eq_kernel_or_section when
coordinates are used. The central quotient and source-section transports
belong to the original-module assembly of Aschbacher–Smith 10.2.9,
printed pp.750–751. Native core data: GLS3 Table 5.3i.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem core_center_card_congr {H : Type*} [Group H] (e : G ≃* H) :
    Nat.card (center (pCore 2 G)) = Nat.card (center (pCore 2 H)) := by
  let ec : pCore 2 G ≃* pCore 2 H :=
    (e.subgroupMap (pCore 2 G)).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 e))
  exact Nat.card_congr (Subgroup.centerCongr ec).toEquiv

private theorem local_twoPerfect (S : Sylow 2 G) (B : Subgroup G)
    (hl : B ∈ localCComponents S) : IsPPerfect 2 B := by
  let := hl.perfect
  let eB := subgroupOfEquivOfLe (show B ≤ B ⊔ (S : Subgroup G) from le_sup_left)
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := eB.toMonoidHom) eB.surjective
  intro N hN hquot
  let := hN
  have hs : Subsingleton (B ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (B ⧸ N) hquot.isNilpotent
  apply eq_top_iff.mpr
  intro b _
  exact (QuotientGroup.eq_one_iff b).mp (Subsingleton.elim _ _)

/-- The original normalized irreducible section cannot lie in the first J₄
involution centralizer. All hypotheses concern the literal supplied B and E. -/
theorem not_jankoFour_first
    (S : Sylow 2 G) (B E : Subgroup G) (hl : B ∈ localCComponents S)
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hSE : (S : Subgroup G) ≤ normalizer (E : Set G))
    (hE : IsElementaryAbelian 2 E) (hEB : E ≤ B) (hc : 16 ≤ Nat.card E)
    (hcore : B.pCoreIn 2 ≤ centralizer (E : Set G)) (hmove : ⁅E,B⁆ = E)
    (hirr : ∀ N : Subgroup G, E ⊓ centralizer (B : Set G) ≤ N → N ≤ E →
      B ≤ normalizer (N : Set G) → N = E ⊓ centralizer (B : Set G) ∨ N = E)
    (e : G ≃* Janko4.InvolutionCentralizers.First.centralizer) : False := by
  let H := Janko4.InvolutionCentralizers.First.centralizer
  have hCnative : centralizer (pCore 2 H : Set H) ≤ pCore 2 H :=
    (@Theory.Quasithin.centralizer_pCore_le_iff H
      Janko4.OuterReduction.FixedGenerator.NormalizerSquares.involutionCentralizer
      inferInstance inferInstance 2 Janko4.InvolutionCentralizers.First.centralizerEquiv).mpr
      Janko4.OuterReduction.FixedGenerator.NormalizerSquares.localTwoCoreCentralizerControl.1
  have hC : centralizer (pCore 2 G : Set G) ≤ pCore 2 G :=
    (@Theory.Quasithin.centralizer_pCore_le_iff G H
      inferInstance inferInstance 2 e).mpr hCnative
  have hh := Theory.GroupAction.fully_moved_irreducible_card_le_core_center
    S B E (local_twoPerfect S B hl) hSB hSE hE hEB hcore hmove hirr hC
  have hz : Nat.card (center (pCore 2 G)) = 2 := by
    rw [@core_center_card_congr G inferInstance H inferInstance e]
    let := Janko4.InvolutionCentralizers.First.centralizer_twoCore_extraspecial
    exact IsExtraspecial.center_order_p 2 (pCore 2 H)
  omega

/-- The weaker chosen-section dichotomy produced by the original central
quotient suffices; its core-centrality orientation is preserved. -/
theorem not_jankoFour_first_of_section_dichotomy
    (S : Sylow 2 G) (B E : Subgroup G) (hl : B ∈ localCComponents S)
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hSE : (S : Subgroup G) ≤ normalizer (E : Set G))
    (hE : IsElementaryAbelian 2 E) (hEB : E ≤ B) (hc : 16 ≤ Nat.card E)
    (hcore : E ≤ centralizer (B.pCoreIn 2 : Set G)) (hmove : ⁅E,B⁆ = E)
    (hirr : ∀ N : Subgroup G, N ≤ E → B ≤ normalizer (N : Set G) →
      N ≤ centralizer (B : Set G) ∨ N ⊔ (E ⊓ centralizer (B : Set G)) = E)
    (e : G ≃* Janko4.InvolutionCentralizers.First.centralizer) : False := by
  apply not_jankoFour_first S B E hl hSB hSE hE hEB hc
    (le_centralizer_iff.mp hcore) hmove ?_ e
  intro N hZN hNE hBN
  rcases hirr N hNE hBN with hNC | hjoin
  · exact Or.inl (le_antisymm (le_inf hNE hNC) hZN)
  · exact Or.inr ((sup_eq_left.mpr hZN).symm.trans hjoin)

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF
