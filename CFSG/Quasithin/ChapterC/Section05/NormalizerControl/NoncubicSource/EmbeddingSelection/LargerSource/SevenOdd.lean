module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.SevenSylow
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.OddThree
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.SurvivingParameters
public import Theory.SpecificGroups.SL2.CardFourEquiv
/-!
# Alternating-seven local subgroups in odd ternary groups

A perfect centerless A7 has two-rank two, so the intrinsic Sylow acts
faithfully by the odd ternary involution-centralizer bound. Its order is
therefore exactly sixteen. The permutation Sylow construction supplies an
actual ambient involution centralizing an injected A5, contradicting the
same rank-one bound. This handles both signs and their special covers.
Source: Aschbacher–Smith A.3.12(9), A.3.21(a), and C.5.12, pp.48,55,163.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open Chapter1.Section02.LocalModels ChapterA.Section03.SourceEmbeddings
open Theory.SpecificGroups.OddThreePerfectCentralizers Theory.SpecificGroups.OddThreeRank
open Theory.SpecificGroups.OddThreeSylowOrder
variable {G : Type*} [Group G] [Finite G]
omit [Finite G] in
private theorem seven_odd_three_centralizer_rank
    {K : Type*} [Group K] [Finite K] [Group.IsPerfect K]
    (hz : center K = ⊥) {p : ℕ} (hp : p.Prime) (ho : Odd p) (u : Bool)
    (hm : IsPSLSign G u 3 p ∨ IsSLSign G u 3 p)
    (t : G) (ht : orderOf t = 2)
    (j : K →* centralizer ({t} : Set G)) (hj : Function.Injective j) :
    primeRank 2 K ≤ 1 := by
  let : Fact p.Prime := ⟨hp⟩
  cases u with
  | false =>
    rcases hm with hm | hm
    · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      let c := Matrix.SU3.InnerThreeRank.centralizerEquiv e t
      exact projective_linear_rank
        (two_ne_zero_of_odd_card ho (k := 1) (by simpa using hF))
        (e t) ((e.orderOf_eq t).trans ht) (c.toMonoidHom.comp j) (c.injective.comp hj)
    · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      let c := Matrix.SU3.InnerThreeRank.centralizerEquiv e t
      exact special_linear_rank
        (two_ne_zero_of_odd_card ho (k := 1) (by simpa using hF))
        (e t) ((e.orderOf_eq t).trans ht) (c.toMonoidHom.comp j) (c.injective.comp hj)
  | true =>
    rcases hm with hm | hm
    · obtain ⟨F,_,_,J,hF,hc,⟨e⟩⟩ := hm
      let c := Matrix.SU3.InnerThreeRank.centralizerEquiv e t
      exact projective_unitary_rank p ho F J hF hc
        (e t) ((e.orderOf_eq t).trans ht) (c.toMonoidHom.comp j) (c.injective.comp hj)
    · obtain ⟨F,_,_,J,hF,hc,⟨e⟩⟩ := hm
      let c := Matrix.SU3.InnerThreeRank.centralizerEquiv e t
      exact special_unitary_rank p ho F J hF hc hz
        (e t) ((e.orderOf_eq t).trans ht) (c.toMonoidHom.comp j) (c.injective.comp hj)


omit [Finite G] in
private theorem odd_three_sixteen_dvd {p : ℕ} (hp : p.Prime) (ho : Odd p) (u : Bool)
    (hm : IsPSLSign G u 3 p ∨ IsSLSign G u 3 p) : 16 ∣ Nat.card G := by
  cases u with
  | false =>
      rcases hm with hm | hm
      · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
        rw [Nat.card_congr e.toEquiv]
        exact projective_sixteen_dvd_card (hF.symm ▸ ho)
      · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
        rw [Nat.card_congr e.toEquiv]
        exact special_sixteen_dvd_card (hF.symm ▸ ho)
  | true =>
      rcases hm with hm | hm
      · obtain ⟨F,_,_,J,hF,hc,⟨e⟩⟩ := hm
        rw [Nat.card_congr e.toEquiv]
        exact unitary_projective_sixteen_dvd_card J hp ho hF hc
      · obtain ⟨F,_,_,J,hF,hc,⟨e⟩⟩ := hm
        rw [Nat.card_congr e.toEquiv]
        exact unitary_special_sixteen_dvd_card J hp ho hF hc

private theorem alternating_five_two_rank_lower : 2 ≤ primeRank 2 (alternatingGroup (Fin 5)) := by
  obtain ⟨e⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (K := GaloisField 2 2) (by rw [GaloisField.card 2 2 (by decide)]; norm_num)
  rw [← primeRank_equiv 2 e]
  exact Theory.PSL2.root_two_rank_ge (GaloisField 2 2)
    (by rw [GaloisField.card 2 2 (by decide)])

theorem not_seven_local_odd_three (T : Sylow 2 G) {B : Subgroup G}
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G)) (hB : IsAlternating B 7)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (u : Bool) :
    ¬ IsPSLSign G u 3 p ∧ ¬ IsSLSign G u 3 p := by
  suffices hh : ¬ (IsPSLSign G u 3 p ∨ IsSLSign G u 3 p) from
    ⟨fun h => hh (.inl h),fun h => hh (.inr h)⟩
  intro hm
  let : Group.IsPerfect B := AlternatingSevenMaximal.perfect_of_model hB
  have hr : 2 ≤ primeRank 2 B := by
    obtain ⟨e⟩ := hB
    rw [primeRank_equiv 2 e,Representation.AlternatingSevenConjugatePair.ElementaryGeometry.primeRank_alternating]
  have hf := odd_three_perfect_sylow_faithful T B
    (AlternatingSevenMaximal.center_of_model hB) hr hp ho u hm
  obtain ⟨t,ht,j,hj⟩ := alternating_seven_sylow_involution_centralizer T B hB hTB hf
    (T.pow_dvd_card_of_pow_dvd_card (n := 4) (odd_three_sixteen_dvd hp ho u hm))
  let A := alternatingGroup (Fin 5)
  let : Group.IsPerfect A := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  have hz : center A=⊥ := by
    let : IsSimpleGroup A := alternatingGroup.isSimpleGroup (by simp)
    exact center_eq_bot_of_simple_perfect
  have hc := seven_odd_three_centralizer_rank hz hp ho u hm t ht j hj
  change primeRank 2 (alternatingGroup (Fin 5)) ≤ 1 at hc
  have hl := alternating_five_two_rank_lower
  omega

theorem not_seven_containing_odd_three (T : Sylow 2 G) {B L : Subgroup G}
    (hL : L.IsSubnormal) (hBL : B ≤ L)
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G)) (hB : IsAlternating B 7)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (u : Bool) :
    ¬ IsPSLSign L u 3 p ∧ ¬ IsSLSign L u 3 p := by
  obtain ⟨S,hS⟩ := T.exists_subgroupOf_eq_of_subnormal L hL
  apply not_seven_local_odd_three S ?_ ⟨(subgroupOfEquivOfLe hBL).trans hB.some⟩ hp ho u
  rw [hS,← subgroupOf_normalizer_eq hBL]
  exact comap_mono hTB
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
