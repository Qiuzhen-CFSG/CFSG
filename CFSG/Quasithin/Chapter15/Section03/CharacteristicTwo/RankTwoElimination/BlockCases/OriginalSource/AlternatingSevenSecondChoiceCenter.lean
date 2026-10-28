module
public import Theory.GroupTheory.PCoreSupplementFixed
public import Theory.GroupTheory.NormalSymmetricThreePairRank.Inner
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.RankTwoCoreCenterAction
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.OriginalSource.SecondChoiceQuotients

/-!
# The second-choice quotient excludes a fixed cubic component center

The original second choice gives Y₊/O₂(Y₊) ≅ E₉ and
Y₊S/O₂(Y₊S) ≅ S₃×S₃. Therefore an S-fixed class in the first
quotient is trivial: its image in the second quotient is central.
The actual cubic center of L/O₂(L) lies in the Y₊ image. If S fixes
this center, a lift y has [S,y] inside Y₊ ∩ O₂(L) ≤ O₂(Y₊), so
its class is fixed and y lies in O₂(Y₊). Its central cubic image
must then be trivial by coprimeness.

The proof deliberately retains the possible surviving two-core in the
Y₊ action. Only restriction of O₂(L), rather than containment of
O₂(Y₊) in O₂(L), is used. The last consumer accepts the literal
inner action supplied by the actual exceptional-seven moved row.
Source: Aschbacher–Smith15.3.11(5) and15.3.21, pp.1123–1124,1127.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
variable {G : Type*} [Group G] [Finite G]

private theorem center_bot_of_symmetricThreePair {E : Type*} [Group E]
    (e : E ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) : center E = ⊥ := by
  rw [eq_bot_iff_forall]
  intro z hz
  apply e.injective
  have h1 : (e z).1 = 1 := NormalSymmetricThreePairRank.symmetricThree_center_trivial _ (by
    intro a
    have he := congrArg (fun t => (e t).1) (mem_center_iff.mp hz (e.symm (a,1)))
    simpa only [map_mul,e.apply_symm_apply,Prod.fst_mul] using he)
  have h2 : (e z).2 = 1 := NormalSymmetricThreePairRank.symmetricThree_center_trivial _ (by
    intro a
    have he := congrArg (fun t => (e t).2) (mem_center_iff.mp hz (e.symm (1,a)))
    simpa only [map_mul,e.apply_symm_apply,Prod.snd_mul] using he)
  simpa only [map_one] using Prod.ext h1 h2

/-- The second-choice quotient has no nontrivial S-fixed residual class. -/
theorem source_rankTwo_secondChoice_fixed_class
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hsecond : OutsideStructure.SecondChoice d)
    (y : G) (hy : y ∈ d.Yplus)
    (hfixed : ∀ s ∈ d.S, ⁅s,y⁆ ∈ d.Yplus.pCoreIn 2) : y ∈ d.Yplus.pCoreIn 2 := by
  obtain ⟨⟨eY⟩,⟨eH⟩⟩ := OutsideStructure.source_rankTwo_secondChoice_quotients
    hG d hempty hM hu hmany hI htwo hsecond
  have h11 := OutsideStructure.source_lemma_15_3_11_from_selection hG d hempty hM hu hmany I hI
  have hSnY : d.S ≤ normalizer (d.Yplus : Set G) := by
    intro s hs
    exact (h11.normalizer_eq.ge ⟨d.sylow_le hs.1,
      (show d.S ≤ I from le_sup_right.trans hI.1.2) hs⟩).2
  have hc : ⁅d.Yplus,d.Yplus⁆ ≤ d.Yplus.pCoreIn 2 := by
    apply (commutator_self_le_pCoreIn_iff 2 _).mpr
    refine ⟨⟨fun a b => eY.injective ?_⟩⟩
    rw [map_mul,map_mul,mul_comm]
  exact mem_pCoreIn_of_supplement_fixed 2 d.Yplus d.S
    (sup_le d.Yplus.le_normalizer hSnY) hc (center_bot_of_symmetricThreePair eH) y hy hfixed

/-- A cubic component center cannot be fixed by the original S action in
this second-choice rank-two configuration. -/
theorem source_rankTwo_secondChoice_cubic_center_false
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hsecond : OutsideStructure.SecondChoice d) (c : ComponentWitness d I)
    (hYL : d.Yplus ≤ c.L) (hc : Nat.card (center (c.L ⧸ pCore 2 c.L)) = 3)
    (hSnL : d.S ≤ normalizer (c.L : Set G))
    (hfix : ∀ (a : normalizer (c.L : Set G)), (a : G) ∈ d.S →
      ∀ z : c.L ⧸ pCore 2 c.L, z ∈ center (c.L ⧸ pCore 2 c.L) →
        quotientAut (pCore 2 c.L) (c.L.normalizerMonoidHom a) z = z) : False := by
  let q := QuotientGroup.mk' (pCore 2 c.L)
  have h11 := OutsideStructure.source_lemma_15_3_11_from_selection hG d hempty hM hu hmany I hI
  have hSnY : d.S ≤ normalizer (d.Yplus : Set G) := by
    intro s hs
    exact (h11.normalizer_eq.ge ⟨d.sylow_le hs.1,
      (show d.S ≤ I from le_sup_right.trans hI.1.2) hs⟩).2
  have hcenter : center (c.L ⧸ pCore 2 c.L) = ⊥ := by
    rw [eq_bot_iff_forall]
    intro z hz
    obtain ⟨y,hy,hyz⟩ := source_rankTwo_cubic_center_le_image hG d hI htwo c hYL hc hz
    change q y = z at hyz
    have hycore : (y : G) ∈ d.Yplus.pCoreIn 2 := by
      apply source_rankTwo_secondChoice_fixed_class hG d hempty hM hu hmany hI htwo hsecond
        (y : G) hy
      intro s hs
      let a : normalizer (c.L : Set G) := ⟨s,hSnL hs⟩
      let t : c.L := c.L.normalizerMonoidHom a y * y⁻¹
      have he : (t : G) = ⁅s,(y : G)⁆ := by
        change ((c.L.normalizerMonoidHom a y : c.L) : G) * (y : G)⁻¹ = _
        rw [normalizerMonoidHom_apply_apply_coe]
        rfl
      have htY : (t : G) ∈ d.Yplus := by
        rw [he]
        exact le_normalizer_iff_commutator_le_right.mp hSnY (commutator_mem_commutator hs hy)
      have htq : q t = 1 := by
        change q (c.L.normalizerMonoidHom a y * y⁻¹) = 1
        rw [map_mul,map_inv,← quotientAut_apply_mk,hyz,hfix a hs z hz,mul_inv_cancel]
      have htcore : (t : G) ∈ c.L.pCoreIn 2 :=
        ⟨t,(QuotientGroup.eq_one_iff _).mp htq,rfl⟩
      rw [← he]
      exact inf_pCoreIn_le_of_le 2 hYL ⟨htY,htcore⟩
    have hy' : y ∈ (d.Yplus.pCoreIn 2).subgroupOf c.L := hycore
    have hp : IsPGroup 2 (((d.Yplus.pCoreIn 2).subgroupOf c.L).map q) :=
      (isPGroup_pCoreIn 2 d.Yplus).comap_subtype.map q
    have hz3 : IsPGroup 3 (center (c.L ⧸ pCore 2 c.L)) :=
      IsPGroup.of_card (n := 1) (by simpa using hc)
    have hdis := hp.disjoint_of_coprime hz3 (by decide)
    exact disjoint_def.mp hdis ⟨y,hy',hyz⟩ hz
  have hcard : Nat.card (center (c.L ⧸ pCore 2 c.L)) = 1 := by
    rw [hcenter]
    simp
  omega
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
variable {G : Type*} [Group G] [Finite G]

/-- Literal consumer of the actual inner-action package. -/
theorem source_rankTwo_secondChoice_cubic_center_false_of_inner
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hsecond : OutsideStructure.SecondChoice d) (c : ComponentWitness d I)
    (hYL : d.Yplus ≤ c.L) (hc : Nat.card (center (c.L ⧸ pCore 2 c.L)) = 3)
    (hn : d.Yplus ⊔ d.S ≤ normalizer (c.L : Set G))
    (hinner : ∀ (a : normalizer (c.L : Set G)), (a : G) ∈ d.S →
      ∃ k : c.L ⧸ pCore 2 c.L,
        quotientAut (pCore 2 c.L) (c.L.normalizerMonoidHom a) = MulAut.conj k) : False := by
  apply source_rankTwo_secondChoice_cubic_center_false
    hG d hempty hM hu hmany hI htwo hsecond c hYL hc (le_sup_right.trans hn)
  intro a ha z hz
  obtain ⟨k,hk⟩ := hinner a ha
  rw [hk,MulAut.conj_apply,mem_center_iff.mp hz k,mul_inv_cancel_right]
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
