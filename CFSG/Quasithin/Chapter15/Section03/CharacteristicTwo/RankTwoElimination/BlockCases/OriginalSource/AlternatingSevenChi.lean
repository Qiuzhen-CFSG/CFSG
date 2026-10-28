module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.AlternatingSeven
public import Theory.SpecificGroups.SymmetricSeven.EightNormalizers
public import Theory.ElementaryAbelian.Injective

/-!
# The ordinary A₇ chi cases in original 15.3.21

C.2.7 identifies the actual radical image in S₇ as a dihedral eight or an
elementary eight. Its normalizer has three-rank at most one. The original
Y₊ normalizes R=O₂(Y₊S), and its map into the radical normalizer has two-group
kernel, contradicting its three-rank two. The source consumer discharges all
earlier containments and normalizer inputs; only the literal C.2.7 model
and radical alternatives remain to be supplied by that classification.

Source: Aschbacher–Smith C.2.7(3) and 15.3.21, printed pp.145–147 and1127.
-/


public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open Chapter1.RadicalExclusions.ModelReduction
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

theorem no_alternatingSeven_of_radical_normalizer_rank
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hR : d.R ≤ normalizer (c.L : Set G))
    (hrank : primeRank 3 d.Yplus = 2) (hYL : d.Yplus ≤ c.L)
    (hblock : ChapterC.IsAlternatingBlock c.L 7)
    (model : SymmetricStarModel c.L d.R 7)
    (hsmall : primeRank 3 (normalizer
      ((starImage c.L d.R d.R).map model.groupIso.toMonoidHom :
        Set (Equiv.Perm (Fin 7)))) ≤ 1) : False := by
  obtain ⟨e⟩ := hblock.2.2.quotient_iso
  have hz : center (c.L ⧸ pCore 2 c.L) = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro x hx
    apply mem_bot.mpr
    have he : e x ∈ center (alternatingGroup (Fin 7)) := (centerCongr e ⟨x,hx⟩).property
    rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at he
    exact e.map_eq_one_iff.mp he
  let eK : starImage c.L d.R c.L ≃* alternatingGroup (Fin 7) :=
    (model.groupIso.subgroupMap _).trans (MulEquiv.subgroupCongr model.component)
  let : Nontrivial (starImage c.L d.R c.L) := eK.symm.injective.nontrivial
  have hne : starImage c.L d.R c.L ≠ ⊥ := (nontrivial_iff_ne_bot _).mp inferInstance
  let a := coreStarEquivOfCenterEqBot hR c.core_quotient_quasisimple hne hz
  let J := c.L ⊔ d.R
  let q := QuotientGroup.mk' (starKernel c.L d.R)
  have hYN : d.Yplus ≤ normalizer (d.R : Set G) :=
    (le_sup_left : d.Yplus ≤ d.Yplus ⊔ d.S).trans
      ((d.Yplus ⊔ d.S).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image (d.Yplus ⊔ d.S)
          (pCore 2 (d.Yplus ⊔ d.S : Subgroup G))))
  have hYNJ : d.Yplus.subgroupOf J ≤ normalizer (d.R.subgroupOf J : Set J) := by
    rw [←subgroupOf_normalizer_eq (show d.R ≤ J from le_sup_right)]
    exact comap_mono hYN
  have hYNstar : starImage c.L d.R d.Yplus ≤
      normalizer (starImage c.L d.R d.R : Set (StarQuotient c.L d.R)) :=
    (map_mono hYNJ).trans ((d.R.subgroupOf J).le_normalizer_map q)
  let B := (starImage c.L d.R d.R).map model.groupIso.toMonoidHom
  have hYNperm : (starImage c.L d.R d.Yplus).map model.groupIso.toMonoidHom ≤
      normalizer (B : Set (Equiv.Perm (Fin 7))) :=
    (map_mono hYNstar).trans ((starImage c.L d.R d.R).le_normalizer_map model.groupIso.toMonoidHom)
  let f : d.Yplus →* Equiv.Perm (Fin 7) := model.groupIso.toMonoidHom.comp
    ((starImage c.L d.R c.L).subtype.comp ((toStarImage c.L d.R).comp (inclusion hYL)))
  have hf (y : d.Yplus) : f y ∈ normalizer (B : Set (Equiv.Perm (Fin 7))) := by
    apply hYNperm
    apply mem_map_of_mem
    exact mem_map_of_mem q y.property
  let g : d.Yplus →* normalizer (B : Set (Equiv.Perm (Fin 7))) := f.codRestrict _ hf
  have hk : IsPGroup 2 g.ker := by
    let j : g.ker →* pCore 2 c.L :=
      ((inclusion hYL).comp g.ker.subtype).codRestrict _ (by
        intro y
        apply (QuotientGroup.eq_one_iff _).mp
        apply a.injective
        change toStarImage c.L d.R (inclusion hYL y.val) = 1
        apply Subtype.ext
        apply model.groupIso.injective
        simp only [Subgroup.coe_one,map_one]
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
  have hb := (primeRank_le_of_coprime_ker 3 g hcop).trans hsmall
  omega

theorem no_alternatingSeven_chi_elementary
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hR : d.R ≤ normalizer (c.L : Set G))
    (hrank : primeRank 3 d.Yplus = 2) (hYL : d.Yplus ≤ c.L)
    (hblock : ChapterC.IsAlternatingBlock c.L 7)
    (he : starImage c.L d.R d.R ≃* Multiplicative (Fin 3 → ZMod 2))
    (model : SymmetricStarModel c.L d.R 7) : False := by
  let B := (starImage c.L d.R d.R).map model.groupIso.toMonoidHom
  let eB : B ≃* Multiplicative (Fin 3 → ZMod 2) :=
    (model.groupIso.subgroupMap _).symm.trans he
  let : IsElementaryAbelian 2 (Multiplicative (Fin 3 → ZMod 2)) := by
    refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    apply Multiplicative.toAdd.injective
    funext i
    rw [pow_two]
    change x.toAdd i + x.toAdd i = 0
    exact CharTwo.add_self_eq_zero _
  have hB : IsElementaryAbelian 2 B := IsElementaryAbelian.of_injective
    eB.toMonoidHom eB.injective
  have hc : Nat.card B = 8 := by
    rw [Nat.card_congr eB.toEquiv]
    change Nat.card (Fin 3 → ZMod 2) = 8
    simp only [Nat.card_fun,Nat.card_zmod,Nat.card_fin]
    norm_num
  exact no_alternatingSeven_of_radical_normalizer_rank d c hR hrank hYL hblock model
    (Theory.SpecificGroups.SymmetricSeven.EightNormalizers.elementary_normalizer_rank B hB hc)

theorem no_alternatingSeven_chi_dihedral
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hR : d.R ≤ normalizer (c.L : Set G))
    (hrank : primeRank 3 d.Yplus = 2) (hYL : d.Yplus ≤ c.L)
    (hblock : ChapterC.IsAlternatingBlock c.L 7)
    (he : starImage c.L d.R d.R ≃* DihedralGroup 4)
    (model : SymmetricStarModel c.L d.R 7) : False := by
  let B := (starImage c.L d.R d.R).map model.groupIso.toMonoidHom
  let eB : B ≃* DihedralGroup 4 := (model.groupIso.subgroupMap _).symm.trans he
  have hB : IsPGroup 2 B := (IsPGroup.of_card (n := 3)
    (show Nat.card (DihedralGroup 4) = 2 ^ 3 by rw [DihedralGroup.nat_card]; norm_num)).of_equiv eB.symm
  have hx : ∃ x ∈ B, x ^ 2 ≠ 1 := by
    let x := eB.symm (DihedralGroup.r 1)
    refine ⟨x,x.property,?_⟩
    intro hh
    have heq : (DihedralGroup.r 1 : DihedralGroup 4) ^ 2 = 1 := by
      have hh' : x ^ 2 = 1 := Subtype.ext hh
      simpa only [map_pow,x,eB.apply_symm_apply,map_one] using congrArg eB hh'
    exact (by decide : (DihedralGroup.r 1 : DihedralGroup 4) ^ 2 ≠ 1) heq
  exact no_alternatingSeven_of_radical_normalizer_rank d c hR hrank hYL hblock model
    (Theory.SpecificGroups.SymmetricSeven.EightNormalizers.noninvolution_normalizer_rank B hB hx)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open Chapter1.RadicalExclusions.ModelReduction
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

/-- The two chi clauses of C.2.7 are incompatible with the original rank-two
subgroup normalizing its actual radical. -/
theorem source_15_3_21_alternatingSeven_chi
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (hrank : primeRank 3 d.Yplus = 2)
    (c : ComponentWitness d I) (hblock : ChapterC.IsAlternatingBlock c.L 7)
    (model : SymmetricStarModel c.L d.R 7)
    (hradical : Nonempty (starImage c.L d.R d.R ≃* DihedralGroup 4) ∨
      Nonempty (starImage c.L d.R d.R ≃* Multiplicative (Fin 3 → ZMod 2))) : False := by
  have h11 := OutsideStructure.source_lemma_15_3_11_from_selection
    hG d hempty hM hu hmany I hI
  obtain ⟨e⟩ := hblock.2.2.quotient_iso
  have hrI : primeRank 3 I ≤ 2 :=
    (OutsideStructure.outside_sqtk hG d hI).stronglyQuasithin 3 (by decide) (by decide)
  have hYL := yplus_le_of_alternatingSeven_quotient d c h11.theta_eq.symm hrI e
  have h12 := ComponentIntersection.source_lemma_15_3_12_1_from_selection
    hG d hempty hM hu hmany hI (component_le c)
    (LinearThree.Extension.SourceCases.component_in_overgroup d c) hrank c.rank_pos
  rcases hradical with he | he
  · obtain ⟨he⟩ := he
    exact no_alternatingSeven_chi_dihedral d c h12.2.1 hrank hYL hblock he model
  · obtain ⟨he⟩ := he
    exact no_alternatingSeven_chi_elementary d c h12.2.1 hrank hYL hblock he model


end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
