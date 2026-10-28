module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.CubicOrbit
public import CFSG.Quasithin.ChapterB.Section06To07.Structure
public import Theory.SpecificGroups.Alternating.FourPairOuter
public import Theory.GroupTheory.SylowOuterCover
public import Theory.GroupTheory.PResidual.PrimeSection

/-!
# An alternating-three orbit fills a minimal parabolic's two-residual

The normal Sylow orbit of an A₃ block is A₄ or A₄², so its outer
automorphism group is a two-group. The orbit, its centralizer and the
Sylow subgroup generate the ambient group. The centralizer and Sylow
cannot generate: two-perfection would put the original block in its
own centralizer. Unique maximality therefore forces the orbit and Sylow
to generate. This identifies the orbit with O² and retains its actual
commuting A₃ factors. No characteristic-subgroup exclusion is assumed.

Source: Aschbacher--Smith C.1.26 and 15.1.22(*), pp.132,1098--1099.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct
open ChapterB
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem cubic_orbit_outer_two (N : Subgroup G)
    (hm : Nonempty (N ≃* alternatingGroup (Fin 4)) ∨
      Nonempty (N ≃* AlternatingFourPair.Model)) : IsPGroup 2 (MulAut.Outer N) := by
  rcases hm with hm | hm
  · obtain ⟨e⟩ := hm
    exact AlternatingFourPair.outer_single_two.of_equiv (MulAut.outerCongr e).symm
  · obtain ⟨e⟩ := hm
    exact AlternatingFourPair.outer_pair_two.of_equiv (MulAut.outerCongr e).symm

theorem alternatingThree_orbit_eq_residual
    (hfit : generalizedFitting G = pCore 2 G) (hr : primeRank 3 G ≤ 2)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (A : Subgroup G) (hb : IsBlock A) (ha : IsAlternatingBlock A 3) :
    conjugateSpanBy A (T : Subgroup G) = pResidual 2 G := by
  let N := conjugateSpanBy A (T : Subgroup G)
  obtain ⟨hn,hm⟩ := cubic_orbit_models hfit hr T A hb ha
  let : N.Normal := hn
  let C := centralizer (N : Set G)
  have hCT : C ⊔ (T : Subgroup G) ≠ ⊤ := by
    intro he
    have hAC : A ≤ C := le_normal_of_isPPerfect_of_le_sup_pGroup A C T
      hb.short.twoPerfect T.isPGroup' (by rw [he]; exact le_top)
    have hz : A ≤ centralizer (A : Set G) :=
      hAC.trans (centralizer_le (le_conjugateSpanBy A (T : Subgroup G)))
    have heA : A = ⊥ := by
      apply le_bot_iff.mp
      intro a ha'
      have hh : (⟨a,ha'⟩ : A) ∈ center A := by
        apply mem_center_iff.mpr
        intro b
        exact Subtype.ext (hz ha' b b.property)
      rw [ha.center_eq_bot,mem_bot] at hh
      exact congrArg Subtype.val hh
    obtain ⟨e⟩ := ha.equiv_alternatingFour
    have hc := (Nat.card_congr e.toEquiv).trans
      (alternatingGroup.card_of_card_eq_four (by norm_num))
    rw [heA,card_bot] at hc
    norm_num at hc
  have hgen : N ⊔ (T : Subgroup G) = ⊤ := by
    by_contra he
    let M := minimalParabolicMax T hP
    have hs := minimalParabolicMax_spec T hP
    have hNM : N ⊔ (T : Subgroup G) ≤ M :=
      hP.1.le_maximal ⟨hs.2,hs.1.covBy_top⟩ le_sup_right (lt_top_iff_ne_top.mpr he)
    have hCM : C ⊔ (T : Subgroup G) ≤ M :=
      hP.1.le_maximal ⟨hs.2,hs.1.covBy_top⟩ le_sup_right (lt_top_iff_ne_top.mpr hCT)
    apply hs.1.ne_top
    apply top_unique
    rw [←sup_centralizer_sup_sylow_eq_top N (cubic_orbit_outer_two N hm) T]
    exact sup_le (sup_le (le_sup_left.trans hNM) (le_sup_left.trans hCM)) hs.2
  apply le_antisymm
  · exact conjugateSpanBy_le (le_pResidual_of_isPPerfect A hb.short.twoPerfect)
      le_normalizer_of_normal
  · exact sInf_le ⟨inferInstance,isPGroup_quotient_of_sup_eq_top N T T.isPGroup' hgen⟩

theorem alternatingThree_residual_product
    (hfit : generalizedFitting G = pCore 2 G) (hr : primeRank 3 G ≤ 2)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (A : Subgroup G) (hb : IsBlock A) (ha : IsAlternatingBlock A 3) :
    ∃ F : Set (Subgroup G), F.Nonempty ∧
      (∀ B ∈ F, IsBlock B ∧ IsAlternatingBlock B 3) ∧
      F.Pairwise (fun B C => ⁅B,C⁆ = ⊥) ∧ sSup F = pResidual 2 G := by
  let F : Set (Subgroup G) := Set.range (fun t : T => A.conjBy (t : G))
  have hblocks : ∀ B ∈ F, IsBlock B ∧ IsAlternatingBlock B 3 := by
    rintro B ⟨t,rfl⟩
    exact ⟨hb.map_equiv (MulAut.conj (t : G)),
      Solvable.isAlternatingBlock_of_equiv ((MulAut.conj (t : G)).subgroupMap A) ha⟩
  refine ⟨F,⟨A,⟨1,by simp [Subgroup.conjBy_one]⟩⟩,hblocks,?_,?_⟩
  · intro B hB C hC hne
    exact blocks_commute (blockCommutationHypothesis_of_fitting hfit)
      (hblocks B hB).1 (hblocks C hC).1 hne
  · rw [sSup_range]
    exact (conjugateSpanBy_eq_iSup_conj A (T : Subgroup G)).symm.trans
      (alternatingThree_orbit_eq_residual hfit hr T hP A hb ha)
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct
