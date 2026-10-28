module

public import CFSG.Quasithin.Chapter2.Section04.CoreNormalizers
public import CFSG.Quasithin.Chapter2.Section01To03.LocalStructure.Control
public import CFSG.Quasithin.ChapterB.Section06To07.Elementary
public import Theory.GroupTheory.Commutator.SimpleSubnormal

/-!
# Reduction to a minimal parabolic with an actual block

Choose, inside a member H of Γₑ₀, a minimal overgroup K of its selected
Sylow S which lies outside M. Every such Sylow overgroup inherits
characteristic two. The full local pair and both starred maximalities
retain K in Γₑ₀ with the identical ambient Sylow image.

Every proper S-overgroup in K lies in M, so M ∩ K is its unique maximal
S-overgroup. The β normalizer condition excludes normality of S in K.
Applying the earlier universal C.1.29 input to K then gives an actual
χ₀-block B outside M. Minimality forces K = ⟨B,S⟩.

This proves the minimal-parabolic reduction used on printed p.528 of
Aschbacher–Smith, §2.4 (combined manuscript, 1 March 2004). It reselects
inside the original H; it does not assert that every chosen block of the
original H has the needed generation property. The sole additional source
input in `exists_minimalBlockSetup` is the existing `LocalC129Input`, whose
source discharge remains with the C.1/local-structure owners. No block
recognition or shadow exclusion is assumed or proved here.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter2
variable {G : Type*} [Group G] [Finite G] {M H K : Subgroup G}

/-- Any Sylow overgroup inside H and outside M retains the full local pair
and the original ambient Sylow subgroup in Γₑ₀. -/
theorem sylow_overgroup_in_gammaEvenZero
    (hH : H ∈ gammaEvenZero (Chapter1.He G) M)
    (S : Sylow 2 H)
    (hpair : ((S : Subgroup H).map H.subtype, H) ∈
      localPairsIn (Chapter1.He G) M H)
    (hSK : (S : Subgroup H).map H.subtype ≤ K)
    (hKH : K ≤ H) (hout : ¬ K ≤ M) :
    K ∈ gammaEvenZero (Chapter1.He G) M ∧
      ((S : Subgroup H).map H.subtype, K) ∈ localPairsIn (Chapter1.He G) M K ∧
      ∃ P : Sylow 2 K,
        (P : Subgroup K).map K.subtype = (S : Subgroup H).map H.subtype := by
  have hQK : twoCore H ≤ K := (pCoreIn_le_sylow H S).trans hSK
  have hcore : twoCore H ≤ twoCore K :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 H) hQK
      (hKH.trans (le_normalizer_twoCore H))
  have hne : K ≠ ⊥ := fun he => hout (he ▸ bot_le)
  have he : K ∈ Chapter1.He G :=
    Chapter1.lemma_1_1_4_4 hne hKH hH.2 (inf_le_left.trans hQK)
  have hp : ((S : Subgroup H).map H.subtype, K) ∈ localPairsIn (Chapter1.He G) M K :=
    ⟨⟨hpair.1.1, he, fun hb => hpair.1.2.2.1 (bot_unique (hb ▸ hcore)), hSK, hout⟩,
      le_rfl⟩
  have hg := localPair_snd_mem_gamma hp.1
  obtain ⟨hK, P, hP⟩ := gammaZero_sylow_transport_of_full_base hH.1 S hg ⟨K, hp⟩
  exact ⟨⟨hK, he⟩, hp, P, hP⟩

omit [Finite G] in
private theorem minimal_parabolic_of_outside_generation (S : Sylow 2 K)
    (hb : (S : Subgroup K).map K.subtype ∈ beta M) (hout : ¬ K ≤ M)
    (hgen : ∀ L : Subgroup K, ¬ L.map K.subtype ≤ M → L ⊔ (S : Subgroup K) = ⊤) :
    IsCoatom (M.subgroupOf K) ∧ ChapterB.IsMinimalParabolicOver S ⊤ := by
  have hSP : (S : Subgroup K) ≤ M.subgroupOf K := by
    intro x hx
    exact hb.2.1 (mem_map_of_mem K.subtype hx)
  have hPne : M.subgroupOf K ≠ ⊤ := fun he => hout (subgroupOf_eq_top.mp he)
  have hproper (N : Subgroup K) (hSN : (S : Subgroup K) ≤ N) (hne : N ≠ ⊤) :
      N ≤ M.subgroupOf K := by
    by_contra h
    have hm : ¬ N.map K.subtype ≤ M := fun hm => h (map_le_iff_le_comap.mp hm)
    exact hne (by simpa only [sup_eq_left.mpr hSN] using hgen N hm)
  have hP : IsCoatom (M.subgroupOf K) := by
    refine ⟨hPne, ?_⟩
    intro N hPN
    by_contra hne
    exact hPN.not_ge (hproper N (hSP.trans hPN.le) hne)
  refine ⟨hP, ?_⟩
  apply (ChapterB.isMinimalParabolicOver_top_iff S).mpr
  refine ⟨⟨M.subgroupOf K, ⟨hP, hSP⟩, ?_⟩, ?_⟩
  · intro N hN
    have hNP := hproper N hN.2 hN.1.ne_top
    by_contra he
    exact hPne (hN.1.2 (M.subgroupOf K) (lt_of_le_of_ne hNP he))
  · intro hn
    let := hn
    have hKN : K ≤ normalizer ((S : Subgroup K).map K.subtype : Set G) := by
      rintro x hx
      exact (S : Subgroup K).le_normalizer_map K.subtype
        (mem_map_of_mem K.subtype (show (⟨x, hx⟩ : K) ∈
          normalizer ((S : Subgroup K) : Set K) by rw [normalizer_eq_top]; trivial))
    exact hout (hKN.trans (hb.2.2.1 _ hb.1 le_rfl hb.2.1))

/-- Reselect a minimal parabolic inside H, preserving its actual Sylow
image and Γₑ₀ membership. Every subgroup outside M generates it with S. -/
theorem exists_minimal_parabolic_in_gammaEvenZero
    (hH : H ∈ gammaEvenZero (Chapter1.He G) M) (S : Sylow 2 H)
    (hpair : ((S : Subgroup H).map H.subtype, H) ∈
      localPairsIn (Chapter1.He G) M H) :
    ∃ K : Subgroup G, K ≤ H ∧ K ∈ gammaEvenZero (Chapter1.He G) M ∧
      ∃ P : Sylow 2 K,
        (P : Subgroup K).map K.subtype = (S : Subgroup H).map H.subtype ∧
        ((P : Subgroup K).map K.subtype, K) ∈ localPairsIn (Chapter1.He G) M K ∧
        IsCoatom (M.subgroupOf K) ∧
        ChapterB.IsMinimalParabolicOver P ⊤ ∧
        ∀ L : Subgroup K, ¬ L.map K.subtype ≤ M → L ⊔ (P : Subgroup K) = ⊤ := by
  let A := (S : Subgroup H).map H.subtype
  let candidates : Set (Subgroup G) := {K | K ≤ H ∧ A ≤ K ∧ ¬ K ≤ M}
  obtain ⟨K, hK, hmin⟩ := candidates.toFinite.exists_minimal
    ⟨H, le_rfl, map_subtype_le _, hpair.1.2.2.2.2⟩
  obtain ⟨hg, hp, P, hP⟩ := sylow_overgroup_in_gammaEvenZero hH S hpair hK.2.1 hK.1 hK.2.2
  have hgen (L : Subgroup K) (hout : ¬ L.map K.subtype ≤ M) :
      L ⊔ (P : Subgroup K) = ⊤ := by
    let D := (L ⊔ (P : Subgroup K)).map K.subtype
    have hDK : D ≤ K := map_subtype_le _
    have hAD : A ≤ D := by
      change (S : Subgroup H).map H.subtype ≤ D
      rw [← hP]
      exact map_mono le_sup_right
    have hDM : ¬ D ≤ M := fun he => hout ((map_mono le_sup_left).trans he)
    have he : D = K := le_antisymm hDK (hmin ⟨hDK.trans hK.1, hAD, hDM⟩ hDK)
    apply map_injective K.subtype_injective
    simpa only [← MonoidHom.range_eq_map, range_subtype] using he
  have hminimal := minimal_parabolic_of_outside_generation P
    (show (P : Subgroup K).map K.subtype ∈ beta M from ?_) hK.2.2 hgen
  · exact ⟨K, hK.1, hg, P, hP, by simpa only [hP] using hp,
      hminimal.1, hminimal.2, hgen⟩
  ·
    simpa only [hP] using hpair.1.1

/-- The selected minimal parabolic and its genuine block and conjugation
module. The block is subnormal in H, not in the original ambient G. -/
structure MinimalBlockSetup (M : Subgroup G) where
  H : Subgroup G
  S : Sylow 2 H
  mem_gammaEvenZero : H ∈ gammaEvenZero (Chapter1.He G) M
  full_pair : ((S : Subgroup H).map H.subtype, H) ∈ localPairsIn (Chapter1.He G) M H
  intersection_maximal : IsCoatom (M.subgroupOf H)
  minimal_parabolic : ChapterB.IsMinimalParabolicOver S ⊤
  block : Subgroup H
  block_type : ChapterC.IsChiZeroBlockIn block
  outside : ¬ block.map H.subtype ≤ M
  moved : block.map H.subtype =
    ⁅block.map H.subtype, Stellmacher.elementaryAbelianMaxJ ((S : Subgroup H).map H.subtype)⁆
  generated : block ⊔ (S : Subgroup H) = ⊤

/-- Construct the p.528 setup from the earlier universal C.1.29 implication.
All local application hypotheses and the block-generation equality are proved. -/
theorem exists_minimalBlockSetup {C : GroupClass} (hG : IsSimpleQTKE C G)
    (source : LocalC129Input C G)
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hH : H ∈ gammaEvenZero (Chapter1.He G) M) :
    ∃ d : MinimalBlockSetup M, d.H ≤ H := by
  have hgamma : H ∈ gamma (Chapter1.He G) M :=
    hH.1.elim (fun h => h.1.1) (fun h => h.1)
  obtain ⟨S, hp, _⟩ := exists_full_localPair_of_gammaEven ⟨hgamma, hH.2⟩
  obtain ⟨K, hKH, hg, P, _, hpair, hmax, hmin, hgen⟩ :=
    exists_minimal_parabolic_in_gammaEvenZero hH S hp
  obtain ⟨blocks⟩ := lemma_2_3_8_4_of_localC129 hG source T hTM hunique hg.1 hg.2
    hpair P le_rfl
  obtain ⟨B, hB, hout, hmoved⟩ := blocks.exists_escapingBlock hpair.1.2.2.2.2
  exact ⟨⟨K, P, hg, hpair, hmax, hmin, B, hB, hout, hmoved, hgen B hout⟩, hKH⟩

end CFSG.Quasithin.Chapter2
