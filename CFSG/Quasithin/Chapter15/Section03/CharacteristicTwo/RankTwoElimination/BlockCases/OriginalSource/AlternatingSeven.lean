module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.AlternatingSix
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface
public import Theory.SpecificGroups.AlternatingSeven.TranspositionCore
public import Theory.Alternating.Aut
public import Theory.Quasithin.CoprimeRank

/-!
# The ordinary A₇ transposition case in original 15.3.21

The original rank bound puts Y₊ inside L via the actual A₇ two-core
quotient. Its image in the marked C.2.7 action centralizes a transposition
of S₇, whose centralizer has three-rank one. The two-group kernel preserves
the three-rank-two contradiction. The final consumer derives the earlier
containment, radical normalizer and theta identities from the original setup.

Source: Aschbacher–Smith 15.3.17 and 15.3.21, printed pp.1126–1127;
the marking is C.2.7(3), printed pp.145–147.
-/


public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open Chapter1.RadicalExclusions.ModelReduction
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

private theorem alternatingSeven_outer_two :
    IsPGroup 2 (MulAut.Outer (alternatingGroup (Fin 7))) := by
  let A := alternatingGroup (Fin 7)
  have hcard : Nat.card (Equiv.Perm (Fin 7) ⧸ A) = 2 ^ 1 := by
    rw [← A.index_eq_card]
    exact alternatingGroup.index_eq_two
  apply (IsPGroup.of_card hcard).of_surjective (MulAut.outerAction A)
  intro x
  obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup A) x
  obtain ⟨σ,rfl⟩ :=
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by decide) (by decide)).surjective a
  exact ⟨QuotientGroup.mk' A σ,rfl⟩

theorem yplus_le_of_alternatingSeven_quotient
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hθ : theta (d.MI I) = d.Yplus) (hrI : primeRank 3 I ≤ 2)
    (e : (c.L ⧸ pCore 2 c.L) ≃* alternatingGroup (Fin 7)) :
    d.Yplus ≤ c.L := by
  let K := c.L.subgroupOf I
  let a : K ≃* c.L := subgroupOfEquivOfLe (component_le c)
  let b : (K ⧸ pCore 2 K) ≃* (c.L ⧸ pCore 2 c.L) :=
    QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let f := b.trans e
  let _ : IsQuasisimple (c.L ⧸ pCore 2 c.L) := c.core_quotient_quasisimple
  let _ : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv b.symm
  have hz : center (K ⧸ pCore 2 K) = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro x hx
    apply mem_bot.mpr
    have he : f x ∈ center (alternatingGroup (Fin 7)) := (centerCongr f ⟨x,hx⟩).property
    rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at he
    exact f.map_eq_one_iff.mp he
  have hrK : 2 ≤ primeRank 3 (K ⧸ pCore 2 K) := by
    rw [primeRank_congr 3 f,
      GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime 7 3 Nat.prime_three (by decide)]
  have ho : IsPGroup 2 (MulAut.Outer (K ⧸ pCore 2 K)) :=
    alternatingSeven_outer_two.of_injective
      (MulAut.outerCongr f).toMonoidHom (MulAut.outerCongr f).injective
  have hK : K = primeToResidual 3 I :=
    (LinearThree.Extension.SourceCases.component_in_overgroup d c).eq_primeToResidual_three_of_rank_outer_two
      hz hrK hrI ho
  rw [←hθ]
  apply (closure_le _).mpr
  rintro x ⟨hx,hx3⟩
  have hres : (⟨x,hx.2⟩ : I) ∈ primeToResidual 3 I := by
    apply mem_primeToResidual_of_pow (n := 1)
    apply Subtype.ext
    change x ^ (3 ^ 1) = 1
    simpa only [pow_one,hx3] using pow_orderOf_eq_one x
  change (⟨x,hx.2⟩ : I) ∈ K
  rw [hK]
  exact hres

private theorem transposition_centralizer_rank (t : Equiv.Perm (Fin 7)) (ht : t.IsSwap) :
    primeRank 3 (centralizer ({t} : Set (Equiv.Perm (Fin 7)))) ≤ 1 := by
  obtain ⟨e⟩ := AlternatingSeven.TranspositionCore.transposition_centralizer_equiv
    (MulEquiv.refl _) t ht
  have hc : Nat.card (centralizer ({t} : Set (Equiv.Perm (Fin 7)))) = 240 := by
    rw [Nat.card_congr e.toEquiv]
    norm_num [Nat.card_prod,Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  apply (primeRank_le_iff_elementary_card_le _).mpr
  intro E hE
  let : IsElementaryAbelian 3 E := hE
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 3 E).exists_card_eq
  have hd : Nat.card E ∣ 3 * 80 := by simpa only [hc] using E.card_subgroup_dvd_card
  have hp : Nat.Coprime (Nat.card E) 80 := by
    rw [hn]
    exact (by decide : Nat.Coprime 3 80).pow_left n
  exact Nat.le_of_dvd (by decide) (hp.dvd_mul_right.mp hd)

theorem no_alternatingSeven_transposition
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hR : d.R ≤ normalizer (c.L : Set G))
    (hθ : theta (d.MI I) = d.Yplus) (hrank : primeRank 3 d.Yplus = 2)
    (hYL : d.Yplus ≤ c.L)
    (hblock : ChapterC.IsAlternatingBlock c.L 7)
    (ha : TranspositionAction c.L d.R 7)
    (hM : starM c.L d.R (d.MI I) = starImage c.L d.R c.L ⊓
      centralizer (starImage c.L d.R d.R : Set (StarQuotient c.L d.R))) : False := by
  obtain ⟨model,r,t,hr,hrR,ht,hconj⟩ := ha
  obtain ⟨e⟩ := hblock.2.2.quotient_iso
  have hz : center (c.L ⧸ pCore 2 c.L) = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro x hx
    apply mem_bot.mpr
    have he : e x ∈ center (alternatingGroup (Fin 7)) := (centerCongr e ⟨x,hx⟩).property
    rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at he
    exact e.map_eq_one_iff.mp he
  let : Nontrivial (starImage c.L d.R c.L) := model.groupIso.symm.injective.nontrivial
  have hne : starImage c.L d.R c.L ≠ ⊥ := (nontrivial_iff_ne_bot _).mp inferInstance
  let a := coreStarEquivOfCenterEqBot hR c.core_quotient_quasisimple hne hz
  let f : d.Yplus →* Equiv.Perm (Fin 7) :=
    (alternatingGroup (Fin 7)).subtype.comp
      (model.groupIso.toMonoidHom.comp ((toStarImage c.L d.R).comp (inclusion hYL)))
  have hf (y : d.Yplus) : f y ∈ centralizer ({t} : Set (Equiv.Perm (Fin 7))) := by
    let k := toStarImage c.L d.R (inclusion hYL y)
    have hyM : (y : G) ∈ d.MI I := (hθ ▸ theta_le (d.MI I)) y.property
    have hkM : (k : StarQuotient c.L d.R) ∈ starM c.L d.R (d.MI I) := by
      exact mem_map_of_mem _ ⟨hyM,hYL y.property⟩
    rw [hM] at hkM
    have hrmem : r ∈ starImage c.L d.R d.R := hrR ▸ subset_closure (Set.mem_singleton r)
    have hkr : (k : StarQuotient c.L d.R) = r * (k : StarQuotient c.L d.R) * r⁻¹ := by
      rw [hkM.2 r hrmem,mul_inv_cancel_right]
    have he := (hconj k k).mp hkr
    apply mem_centralizer_singleton_iff.mpr
    change (model.groupIso k : Equiv.Perm (Fin 7)) * t = t * model.groupIso k
    exact (eq_mul_inv_iff_mul_eq.mp he)
  let g : d.Yplus →* centralizer ({t} : Set (Equiv.Perm (Fin 7))) := f.codRestrict _ hf
  have hk : IsPGroup 2 g.ker := by
    let j : g.ker →* pCore 2 c.L :=
      ((inclusion hYL).comp g.ker.subtype).codRestrict _ (by
        intro y
        apply (QuotientGroup.eq_one_iff _).mp
        apply a.injective
        change toStarImage c.L d.R (inclusion hYL y.val) = 1
        apply model.groupIso.injective
        rw [map_one]
        apply Subtype.ext
        have hh : f y.val = 1 := congrArg Subtype.val (show g y.val = 1 from y.property)
        exact hh)
    exact pCore_isPGroup.of_injective j (by
      intro x y hh
      apply Subtype.ext
      apply (inclusion_injective hYL)
      exact congrArg Subtype.val hh)
  obtain ⟨n,hn⟩ := hk.exists_card_eq
  have hcop : Nat.Coprime 3 (Nat.card g.ker) := by
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hb := (primeRank_le_of_coprime_ker 3 g hcop).trans (transposition_centralizer_rank t ht)
  omega

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open Chapter1.RadicalExclusions.ModelReduction
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

/-- The transposition clause of C.2.7 cannot occur in original 15.3.21. -/
theorem source_15_3_21_alternatingSeven_transposition
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (hrank : primeRank 3 d.Yplus = 2)
    (c : ComponentWitness d I) (hblock : ChapterC.IsAlternatingBlock c.L 7)
    (ha : TranspositionAction c.L d.R 7)
    (hm : starM c.L d.R (d.MI I) = starImage c.L d.R c.L ⊓
      centralizer (starImage c.L d.R d.R : Set (StarQuotient c.L d.R))) : False := by
  have h11 := OutsideStructure.source_lemma_15_3_11_from_selection
    hG d hempty hM hu hmany I hI
  obtain ⟨e⟩ := hblock.2.2.quotient_iso
  have hrI : primeRank 3 I ≤ 2 :=
    (OutsideStructure.outside_sqtk hG d hI).stronglyQuasithin 3 (by decide) (by decide)
  have hYL := yplus_le_of_alternatingSeven_quotient d c h11.theta_eq.symm hrI e
  have h12 := ComponentIntersection.source_lemma_15_3_12_1_from_selection
    hG d hempty hM hu hmany hI (component_le c)
    (LinearThree.Extension.SourceCases.component_in_overgroup d c) hrank c.rank_pos
  exact no_alternatingSeven_transposition d c h12.2.1 h11.theta_eq.symm hrank hYL hblock ha hm

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource

