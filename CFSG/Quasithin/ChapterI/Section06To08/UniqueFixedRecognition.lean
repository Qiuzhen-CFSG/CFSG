module

public import CFSG.Quasithin.ChapterI.Section06To08.StrongEmbedding
public import CFSG.Quasithin.ChapterI.Section06To08.TightlyEmbeddedRecognition
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.GroupTheory.TightlyEmbedded.ElementaryClosure
public import Theory.GroupTheory.Covering

/-!
# Recognition of the normal closure in I.8.5

The unique-fixed-coset hypothesis makes the intersection of M with any
external conjugate of V trivial. This supplies the exact tight-embedding and
odd-conjugate-normalizer hypotheses of I.8.2. Its generated involution subgroup
is the normal closure of the original V. In the Bender branch its odd core
centralizes V, hence all of the normal closure; perfectness then gives the
quasisimple conclusion. The rank-one branch gives |V| = 2 and L = O(L)V.

This proves the recognition and central-odd-core part of I.8.5. The omega
identification and solvability of the induced automorphism group are separate
model-action conclusions.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, I.8.3--I.8.5, printed p. 430.
-/

noncomputable section
namespace CFSG.Quasithin.ChapterI.Section06To08
open Theory.GroupTheory BenderSuzuki PFAppendixIII PFchapter1section1
open Subgroup

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Unique fixed cosets give trivial intersection with every conjugate of V
whose conjugator is outside M. -/
public theorem unique_fixed_cosets_conjugate_inter_eq_bot
    {V M : Subgroup G} (hVM : V ≤ M)
    (hfix : ∀ v : G, v ∈ V → v ≠ 1 → ∃! q : G ⧸ M, v • q = q)
    {g : G} (hg : g ∉ M) :
    M ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ := by
  apply eq_bot_iff.mpr
  rintro x ⟨hxM, v, hv, rfl⟩
  by_cases hv1 : v = 1
  · simp [hv1]
  · exact (hg (unique_fixed_cosets_transporter hVM hfix hv hv1 hxM)).elim

private theorem oddCore_normalClosure_le_center
    (V M : Subgroup G) [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G))
    (hO : pPrimeCore 2 (normalClosure (V : Set G)) ≤
      M.comap (normalClosure (V : Set G)).subtype) :
    pPrimeCore 2 (normalClosure (V : Set G)) ≤
      center (normalClosure (V : Set G)) := by
  let L := normalClosure (V : Set G)
  let O := pPrimeCore 2 L
  let N := O.map L.subtype
  let : N.Normal := ConjAct.normal_of_characteristic_of_normal
  have hNM : N ≤ M := by
    rintro _ ⟨x, hx, rfl⟩
    exact hO hx
  have hNodd : Odd (Nat.card N) := by
    rw [show Nat.card N = Nat.card O from card_map_of_injective L.subtype_injective]
    exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (G := L) (p := 2))
  obtain ⟨n, hncard⟩ := IsPGroup.iff_card.mp (IsElementaryAbelian.isPGroup 2 V)
  have hd : Disjoint V N := disjoint_of_coprime_natCard (by
    rw [hncard]
    exact hNodd.coprime_two_left.pow_left n)
  have hc : ⁅V, N⁆ ≤ V ⊓ N := le_inf
    (le_normalizer_iff_commutator_le_left.mp (hNM.trans hn))
    (le_normalizer_iff_commutator_le_right.mp (by
      rw [N.normalizer_eq_top]
      exact le_top))
  have hVN : V ≤ centralizer (N : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp (eq_bot_iff.mpr (hd.eq_bot ▸ hc))
  have hLN : L ≤ centralizer (N : Set G) := normalClosure_le_normal hVN
  intro x hx
  apply mem_center_iff.mpr
  intro y
  apply Subtype.ext
  exact (hLN y.property x (mem_map_of_mem L.subtype hx)).symm

/-- The source I.8.5 hypotheses already recognize the original normal
closure: either the full order-two/odd-core alternative, or a quasisimple
central odd cover of a simple Bender group with the specified quotient Borel.
No tight-embedding, ZD, or recognition premise remains. -/
public theorem lemma_I_8_5_oddCore_recognition
    (V M : Subgroup G) [IsElementaryAbelian 2 V] [(V.subgroupOf M).Normal]
    (hVM : V ≤ M) (hVne : V ≠ ⊥) (hproper : M ≠ ⊤)
    (hfix : ∀ v : G, v ∈ V → v ≠ 1 → ∃! q : G ⧸ M, v • q = q) :
    let L := normalClosure (V : Set G)
    let O := pPrimeCore 2 L
    (Nat.card V = 2 ∧ O ⊔ V.subgroupOf L = ⊤) ∨
      (IsQuasisimple L ∧ BenderSuzuki.IsSimpleBenderGroup (L ⧸ O) ∧
        O = center L ∧ O ≤ M.comap L.subtype ∧
        IsBorelSubgroup ((M.comap L.subtype).map (QuotientGroup.mk' O))) := by
  have hn : M ≤ normalizer (V : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hVM).mp inferInstance
  have hnEq := normalizer_eq_of_unique_fixed_cosets hVM hVne hn hfix
  have hVEven : Even (Nat.card V) := by
    let : Nontrivial V := (nontrivial_iff_ne_bot V).mpr hVne
    obtain ⟨n, hn0, hcard⟩ :=
      (IsElementaryAbelian.isPGroup 2 V).nontrivial_iff_card.mp inferInstance
    exact even_iff_two_dvd.mpr (hcard ▸ dvd_pow_self 2 hn0.ne')
  have hodd : HasOddConjugateNormalizers V := by
    intro g hg
    rw [hnEq] at hg ⊢
    rw [unique_fixed_cosets_conjugate_inter_eq_bot hVM hfix hg]
    simp
  have htight : IsTightlyEmbedded V := by
    refine ⟨hVEven, fun g hg => ?_⟩
    have hd := unique_fixed_cosets_conjugate_inter_eq_bot hVM hfix
      (show g ∉ M by rwa [hnEq] at hg)
    have hi : V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ :=
      eq_bot_iff.mpr ((inf_le_inf_right _ hVM).trans hd.le)
    rw [hi]
    simp
  have hrec := lemma_I_8_2 V htight
    (not_normal_of_unique_fixed_cosets hVM hVne hproper hn hfix) hodd
  dsimp only at hrec
  rw [involutionConjugates_closure_eq_normalClosure V, hnEq] at hrec
  let L := normalClosure (V : Set G)
  let O := pPrimeCore 2 L
  have hVL : V ≤ L := le_normalClosure
  rcases hrec with ⟨hr, hfactor⟩ | ⟨hperfect, hmodel, hO, hB⟩
  · left
    have hcard : Nat.card V ≤ 2 := by
      have hbound := (primeRank_le_iff_elementary_card_le L).mp hr.le
        (V.subgroupOf L) (IsElementaryAbelian.subgroupOf hVL)
      have he := Nat.card_congr (subgroupOfEquivOfLe hVL).toEquiv
      simpa only [he, pow_one] using hbound
    have hcard2 : Nat.card V = 2 := by
      have hpos : 1 < Nat.card V := (one_lt_card_iff_ne_bot V).mpr hVne
      omega
    refine ⟨hcard2, ?_⟩
    obtain ⟨⟨v, hv⟩, hne⟩ := ne_bot_iff_exists_ne_one.mp hVne
    let z : L := ⟨v, hVL hv⟩
    have hzZ : (z : G) ∈ involutionConjugates V :=
      mem_involutionConjugates hv ⟨fun he => hne (Subtype.ext he),
        elemPow_eq_one_of_isElementaryAbelian v hv⟩
    apply top_unique
    rw [← hfactor z hzZ]
    exact sup_le_sup_left (zpowers_le.mpr (show z ∈ V.subgroupOf L from hv)) O
  · right
    have hOc : O ≤ center L := oddCore_normalClosure_le_center V M hn hO
    have hcO : center L ≤ O := by
      have hcQ : center (L ⧸ O) = ⊥ :=
        (hmodel.isSimple.eq_bot_or_eq_top_of_normal _ inferInstance).resolve_right
          (fun ht => hmodel.not_commutative (isMulCommutative_iff.mp
            (center_eq_top_iff.mp ht)))
      intro z hz
      apply (QuotientGroup.eq_one_iff z).mp
      apply mem_bot.mp
      rw [← hcQ]
      apply mem_center_iff.mpr
      intro y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective O y
      exact (map_mul _ x z).symm.trans
        ((congrArg (QuotientGroup.mk' O) (mem_center_iff.mp hz x)).trans (map_mul _ z x))
    have hcent : O = center L := le_antisymm hOc hcO
    have hquasi : IsQuasisimple L := by
      apply (isQuasisimple_def L).mpr
      refine ⟨hperfect, ?_⟩
      exact (QuotientGroup.quotientMulEquivOfEq hcent).isSimpleGroup_congr.mp hmodel.isSimple
    exact ⟨hquasi, hmodel, hcent, hO, hB⟩

end CFSG.Quasithin.ChapterI.Section06To08
