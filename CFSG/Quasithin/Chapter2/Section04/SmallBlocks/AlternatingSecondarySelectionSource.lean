module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingSecondarySylowSource
public import CFSG.Quasithin.Chapter2.Section01To03.Selection.Maximal
public import Theory.GroupTheory.InvolutionCentralizerControl
/-!
# Selecting the secondary involution centralizer

In the single alternating-five branch of 2.4.29, the marked involution centralizes
J(S), its centralizer in M is T_u, and [T:T_u]=2. The beta subgroup and the local
normalizer control then put C_G(u) in Gamma* and retain T_u as its actual Sylow
subgroup. This packages the selection step on page 545; the finite marked
involution calculation supplies the explicit hypotheses.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter2
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.single_alternating_secondary_selection_of_marks
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (hA : ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (u : G) (hu2 : orderOf u = 2)
    (huR : u ∈ (center (elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype))).map
      (elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)).subtype)
    (hout : ¬ d.H ⊓ centralizer ({u} : Set G) ≤ M)
    (hMu : M ⊓ centralizer ({u} : Set G) = (T : Subgroup G) ⊓ centralizer ({u} : Set G))
    (hi : ((T : Subgroup G) ⊓ centralizer ({u} : Set G)).relIndex (T : Subgroup G) = 2) :
    let R := elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    let C := centralizer ({u} : Set G)
    (R,d.H ⊓ C) ∈ localPairsIn (Chapter1.He G) M C ∧
      C ∈ gammaMax (Chapter1.He G) M ∧
      ∃ P : Sylow 2 C, (P : Subgroup C).map C.subtype = (T : Subgroup G) ⊓ C := by
  let R := elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
  let C := centralizer ({u} : Set G)
  let W := zpowers u
  have hRS : R ≤ (d.S : Subgroup d.H).map d.H.subtype := sSup_le fun _ h => h.1
  have hRH : R ≤ d.H := hRS.trans (map_subtype_le _)
  have huRi : u ∈ R := map_subtype_le _ huR
  have huH : u ∈ d.H := hRH huRi
  have huT : u ∈ (T : Subgroup G) := hST.le (hRS huRi)
  have hWcard : Nat.card W = 2 := by rw [Nat.card_zpowers,hu2]
  have hp : IsPGroup 2 W := IsPGroup.of_card (n:=1) (by simpa using hWcard)
  have hne : W ≠ ⊥ := by intro hh; rw [hh,card_bot] at hWcard; omega
  have hWH : W ≤ d.H := zpowers_le.mpr huH
  have hc : centralizer (W : Set G)=C := by
    rw [show W = zpowers u from rfl,zpowers_eq_closure,centralizer_closure]
  have hn : normalizer (W : Set G)=C :=
    le_antisymm ((normalizer_le_centralizer_of_card_two W hWcard).trans hc.le)
      (hc.symm ▸ Subgroup.centralizer_le_normalizer _)
  have hWC : W ≤ C := hn ▸ W.le_normalizer
  have hHu : d.H ⊓ C ∈ Chapter1.He G := by
    rw [←hn]
    exact Chapter1.normalizer_mem_He_of_isPGroup d.mem_gammaEvenZero.2 hp hWH
  have hcoreHu : W ≤ twoCore (d.H ⊓ C) :=
    le_pCoreIn_of_normalizes hp (le_inf hWH hWC) (hn.symm ▸ inf_le_right)
  have hcoreC : W ≤ twoCore C := le_pCoreIn_of_normalizes hp hWC hn.ge
  have hR : R ∈ beta M := d.thompson_beta_of_index_two hG T hM hTM hu hST
    (d.single_alternating_family_action hG T hST hsingle hA).1
  have hRC : R ≤ C := by
    obtain ⟨w,hw,hwv⟩ := huR
    intro r hr
    apply mem_centralizer_singleton_iff.mpr
    rw [←hwv]
    exact congrArg Subtype.val (mem_center_iff.mp hw ⟨r,hr⟩)
  have hpair : (R,d.H ⊓ C) ∈ localPairsIn (Chapter1.He G) M C :=
    ⟨⟨hR,hHu,fun hh => hne (bot_unique (hh ▸ hcoreHu)),le_inf hRH hRC,hout⟩,inf_le_right⟩
  have hgamma : C ∈ gamma (Chapter1.He G) M :=
    ⟨fun hh => hne (bot_unique (hh ▸ hcoreC)),(R,d.H ⊓ C),hpair⟩
  obtain ⟨_,⟨P,hP⟩,_⟩ := secondary_centralizer_sylow_of_index_two T hu u hu2 huT hMu hi
  have hmax := (lemma_2_3_7_1 T hTM hu hgamma P (hP.symm ▸ inf_le_left)
    (hP.symm ▸ hi)).1
  exact ⟨hpair,hmax,P,hP⟩
end CFSG.Quasithin.Chapter2
