module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.AbsorptionSource
public import CFSG.Quasithin.ChapterA.Section04.Signalizers.Global
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.ModuleLift
public import Theory.GroupTheory.PGroupNormalizerContainment
/-!
# Two-cores of overgroups of the original natural block

A.4.2 applied in N(Q)=N(L), with the original Sylow S, makes Q a maximal
L-invariant two-subgroup. Adjoining Q therefore puts every such subgroup
inside Q. For an arbitrary X containing L, apply this to N_{O₂(X)}(Q).
The p-group normalizer condition gives O₂(X)≤Q. The short-block normal
layer dichotomy then gives O₂(X)≤Z(L), unless X normalizes L.

This proves the complete uniqueness conclusion 2.4.11(2) when Z(L)=1.
The nontrivial-center case retains the genuine overcomponent contradiction.
Source: Aschbacher–Smith, Lemma 2.4.11, printed pp.531–532.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open ChapterA.Section04 ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem source_invariant_twoGroup_le_core
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (V : Subgroup G) (hV : IsPGroup 2 V)
    (hVN : V ≤ normalizer (twoCore d.H : Set G))
    (hLV : d.block.map d.H.subtype ≤ normalizer (V : Set G)) : V ≤ twoCore d.H := by
  let L := d.block.map d.H.subtype
  let Q := twoCore d.H
  let N := normalizer (Q : Set G)
  have hLN : L ≤ N := (map_subtype_le _).trans (le_normalizer_twoCore d.H)
  have hNL : N ≤ normalizer (L : Set G) :=
    (lemma_2_4_11_1 d hG T hST hsingle hL hM hTM hunique).le
  have hK := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  have hMe : M ∈ Chapter1.He G := Chapter1.mem_He_iff.mpr (hG.evenCharacteristic T M hM hTM)
  obtain ⟨_,_,P,hP⟩ := lemma_2_4_3_1 hG.evenCharacteristic hMe d.mem_gammaEvenZero d.full_pair d.S le_rfl
  have hm := normal_sylow_core_isMaximal L N hLN hNL hK.2.1.twoPerfect P
  have hgen : L ⊔ (P : Subgroup N).map N.subtype=d.H := by
    rw [hP]
    simpa only [hsingle] using d.ambient_L0_sup_sylow
  rw [hgen] at hm
  have hU : IsTwoSignalizer L N (Q ⊔ V) := (isTwoSignalizer_iff _ _ _).mpr ⟨sup_le Q.le_normalizer hVN,
    (isPGroup_pCoreIn 2 d.H).to_sup_of_normal_left' hV hVN,
    (le_inf ((map_subtype_le _).trans (le_normalizer_twoCore d.H)) hLV).trans
      (normalizer_inf_normalizer_le_normalizer_sup Q V)⟩
  exact le_sup_right.trans ((isMaximalTwoSignalizer_iff _ _ _).mp hm |>.2 _ hU le_sup_left)

theorem source_overgroup_core_le
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (X : Subgroup G) (hLX : d.block.map d.H.subtype ≤ X) : twoCore X ≤ twoCore d.H := by
  let L := d.block.map d.H.subtype
  let Q := twoCore d.H
  let N := normalizer (Q : Set G)
  let P := twoCore X
  have hLQ : L ≤ N := (map_subtype_le _).trans (le_normalizer_twoCore d.H)
  have hLP : L ≤ normalizer (P : Set G) := hLX.trans (le_normalizer_twoCore X)
  have hPN : IsPGroup 2 (P ⊓ N : Subgroup G) := (isPGroup_pCoreIn 2 X).to_le inf_le_left
  have hLn : L ≤ normalizer ((P ⊓ N : Subgroup G) : Set G) :=
    (le_inf hLP (hLQ.trans N.le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hNN := source_invariant_twoGroup_le_core d hG T hST hsingle hL hM hTM hunique
    (P ⊓ N) hPN inf_le_right hLn
  have hQL : Q ≤ L := by
    change twoCore d.H ≤ L
    rw [←(lemma_2_4_8_2 d hG T hST hsingle hL hM hTM hunique).2]
    exact map_subtype_le _
  exact le_of_normalized_pGroup_inf_normalizer_le Q P (isPGroup_pCoreIn 2 d.H)
    (isPGroup_pCoreIn 2 X) (hQL.trans hLP) hNN

theorem source_overgroup_core_central_or_normalizes
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (X : Subgroup G) (hLX : d.block.map d.H.subtype ≤ X) :
    let L := d.block.map d.H.subtype
    twoCore X ≤ (center L).map L.subtype ∨ X ≤ normalizer (L : Set G) := by
  let L := d.block.map d.H.subtype
  let P := twoCore X
  have hPU : P ≤ sourceModule L := by
    rw [(lemma_2_4_8_2 d hG T hST hsingle hL hM hTM hunique).2]
    exact source_overgroup_core_le d hG T hST hsingle hL hM hTM hunique X hLX
  have hPL : P ≤ L := hPU.trans (map_subtype_le _)
  let : (P.subgroupOf L).Normal := normal_subgroupOf_of_le_normalizer (hLX.trans (le_normalizer_twoCore X))
  have hP'U : P.subgroupOf L ≤ ChapterC.blockU L := by
    intro p hp
    obtain ⟨u,hu,he⟩ := hPU hp
    exact (Subtype.ext he : u=p) ▸ hu
  have hK := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  rcases ChapterC.RankOne.ChiProduct.short_normal_layer_dichotomy hK.2.1 (P.subgroupOf L) hP'U with hc | he
  · exact Or.inl (by
      have hh := map_mono (f:=L.subtype) hc
      rwa [map_subgroupOf_eq_of_le hPL] at hh)
  · have hPQ : P=twoCore d.H := by
      have hh := congrArg (map L.subtype) he
      rw [map_subgroupOf_eq_of_le hPL] at hh
      exact hh.trans (lemma_2_4_8_2 d hG T hST hsingle hL hM hTM hunique).2
    exact Or.inr ((le_normalizer_twoCore X).trans
      (by change normalizer (P : Set G) ≤ normalizer (L : Set G)
          rw [hPQ];exact (lemma_2_4_11_1 d hG T hST hsingle hL hM hTM hunique).le))

theorem source_centerless_overgroup_normalizes
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hZ : center (d.block.map d.H.subtype) = ⊥)
    (X : Subgroup G) (hX : X ∈ Chapter1.H G) (hLX : d.block.map d.H.subtype ≤ X) :
    X ≤ normalizer (d.block.map d.H.subtype : Set G) := by
  rcases source_overgroup_core_central_or_normalizes d hG T hST hsingle hL hM hTM hunique X hLX with hc | hn
  · rw [hZ,Subgroup.map_bot] at hc
    exact (hX (bot_unique hc)).elim
  · exact hn

/-- Original 2.4.11(2) in the centerless case. -/
theorem lemma_2_4_11_2_of_centerless
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hZ : center (d.block.map d.H.subtype) = ⊥) :
    IsMaximalTwoLocal (normalizer (twoCore d.H : Set G)) ∧
      {X : Subgroup G | IsMaximalTwoLocal X ∧ d.block.map d.H.subtype ≤ X} =
        {normalizer (twoCore d.H : Set G)} := by
  let L := d.block.map d.H.subtype
  have hn := lemma_2_4_11_1 d hG T hST hsingle hL hM hTM hunique
  have hQne : twoCore d.H ≠ ⊥ :=
    (d.mem_gammaEvenZero.1.elim (fun h => h.1.1) (fun h => h.1)).1
  have hlocal : IsTwoLocal (normalizer (L : Set G)) := hn ▸
    (show IsTwoLocal (normalizer (twoCore d.H : Set G)) from
      ⟨twoCore d.H,hQne,isPGroup_pCoreIn 2 d.H,rfl⟩)
  have h := unique_maximalTwoLocal_overgroup_of_normal L ⊥ bot_le
    ⟨normalizer (L : Set G),hlocal,le_rfl⟩ (by
      intro X hX hLX
      rw [sup_bot_eq] at hLX
      exact normal_subgroupOf_of_le_normalizer
        (source_centerless_overgroup_normalizes d hG T hST hsingle hL hM hTM hunique hZ
          X (Chapter1.mem_H_of_isTwoLocal hX.1) hLX))
  change normalizer (twoCore d.H : Set G) = normalizer (L : Set G) at hn
  rw [hn]
  simpa only [sup_bot_eq] using h
end CFSG.Quasithin.Chapter2.LinearShadows.Single
