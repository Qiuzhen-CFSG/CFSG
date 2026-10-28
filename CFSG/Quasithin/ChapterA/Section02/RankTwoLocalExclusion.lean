module
public import CFSG.Quasithin.ChapterA.Section02.Statements.Models
public import Theory.Alternating.PrimeRank
public import Theory.SpecificGroups.Alternating.TwoThreeCycles
public import CFSG.Quasithin.MainConverse.EvenLinearLocal.LinearThreeGeometry
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.PerfectSubgroups
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.TwoLocalCover
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.PerfectSubgroups
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover
public import Theory.AtlasPort.LinearGroups.G2.PerfectSubgroups
public import Theory.SpecificGroups.Triality.InvolutionFixedRank
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.TwoLocalOrders
public import Theory.SpecificGroups.Tits.TwoLocalFifteenFree
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived


/-!
# Excluding a local A₆ section in the rank-two catalogue

A perfect subgroup with two-core quotient A₆ has three-rank at least two
and order divisible by fifteen. If it normalizes a nontrivial two-subgroup,
the parabolic covers for PSL₃, PSp₄, G₂ and triality put it in a perfect
local subgroup of three-rank at most one. The Ree and Tits local orders
exclude fifteen, while the small G₂ row excludes five. Two-rank at least
four excludes the small symplectic row A₆ itself.

The normalizer is that of the supplied actual two-subgroup; no full-Sylow
normalization or ambient simplicity is assumed.
Source: Aschbacher--Smith, Theorem C (A.2.3) and its local inspection in
12.6.12, printed pp.32 and 825--826.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02

private theorem transport_local_marking
    {A U : Type*} [Group A] [Group U] [Finite A] [Finite U]
    (P R : Subgroup A) [Group.IsPerfect P]
    (hr : 2 ≤ primeRank 3 P) (hd : 15 ∣ Nat.card P)
    (hR : R ≠ ⊥) (hp : IsPGroup 2 R) (hn : P ≤ normalizer (R : Set A))
    (e : A ≃* U) :
    ∃ B W : Subgroup U, Group.IsPerfect B ∧ 2 ≤ primeRank 3 B ∧
      15 ∣ Nat.card B ∧ W ≠ ⊥ ∧ IsPGroup 2 W ∧ B ≤ normalizer (W : Set U) := by
  let a := P.equivMapOfInjective e.toMonoidHom e.injective
  refine ⟨P.map e.toMonoidHom,R.map e.toMonoidHom,
    Group.IsPerfect.ofSurjective (f := a.toMonoidHom) a.surjective,?_,?_,?_,hp.map _,?_⟩
  · rwa [←primeRank_equiv 3 a]
  · rwa [card_map_of_injective e.injective]
  · exact fun he => hR ((map_eq_bot_iff_of_injective R e.injective).mp he)
  · exact (map_mono hn).trans (R.le_normalizer_map e.toMonoidHom)

/-- No rank-two Theorem C model of two-rank at least four contains this actual local A₆ section. -/
theorem not_rankTwo_of_A6_twoLocal
    {A : Type*} [Group A] [Finite A]
    (P R : Subgroup A) [Group.IsPerfect P]
    (heA : Nonempty ((P ⧸ pCore 2 P) ≃* alternatingGroup (Fin 6)))
    (hR : R ≠ ⊥) (hp : IsPGroup 2 R) (hn : P ≤ normalizer (R : Set A))
    (h2 : 4 ≤ primeRank 2 A) {n : ℕ}
    (hm : IsTheoremCRankTwoModel A n) : False := by
  obtain ⟨eA⟩ := heA
  have hr : 2 ≤ primeRank 3 P := by
    rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 P) pCore_isPGroup,
      primeRank_equiv 3 eA]
    exact alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide)
  have hd : 15 ∣ Nat.card P := by
    apply dvd_trans _ (card_quotient_dvd_card (pCore 2 P))
    rw [Nat.card_congr eA.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    decide
  cases hm with
  | linear hn' hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    obtain ⟨B,W,hperf,hr,hd,hW,hp,hn⟩ := transport_local_marking P R hr hd hR hp hn e
    let := hperf
    by_cases hn1 : n = 1
    · have hh := hd.trans B.card_subgroup_dvd_card
      rw [Matrix.PSL3.LinearThree.card_projective,hF,hn1] at hh
      norm_num at hh
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    obtain ⟨g,point,hg⟩ := MainConverse.LinearThreeGeometry.twoLocal_conjugate_le F
      (by omega) hF (normalizer (W : Set _)) ⟨W,hW,hp,rfl⟩
    let j := (MulAut.conj g).toMonoidHom.comp B.subtype
    have hj : j.range ≤ (normalizer (W : Set _)).map (MulAut.conj g).toMonoidHom := by
      rintro _ ⟨b,rfl⟩
      exact mem_map_of_mem _ (hn b.property)
    apply Matrix.PSL3.LinearThree.PerfectSubgroups.no_perfect_odd_rank_two_in_parabolic F
      (by decide : Odd 3) hr (by
        rw [hF]
        exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ n)) j
      ((MulAut.conj g).injective.comp B.subtype_injective)
    cases point with
    | false => exact .inr (hj.trans hg)
    | true => exact .inl (hj.trans hg)
  | symplectic hn' hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    let a := e.trans (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := F)).symm
    obtain ⟨B,W,hperf,hr,_,hW,hp,hn⟩ := transport_local_marking P R hr hd hR hp hn a
    let := hperf
    obtain ⟨g,hg⟩ := Theory.SpecificGroups.SymplecticFour.twoLocal_parabolic_cover_of_charTwo
      (normalizer (W : Set _)) ⟨W,hW,hp,rfl⟩
    let j := (MulAut.conj g).toMonoidHom.comp B.subtype
    have hj : j.range ≤ (normalizer (W : Set _)).map (MulAut.conj g).toMonoidHom := by
      rintro _ ⟨b,rfl⟩
      exact mem_map_of_mem _ (hn b.property)
    exact Theory.SpecificGroups.SymplecticFour.no_perfect_odd_rank_two_in_parabolic
      (by decide : Odd 3) hr j ((MulAut.conj g).injective.comp B.subtype_injective)
      (hg.imp hj.trans hj.trans)
  | g2 hn' hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    obtain ⟨B,W,hperf,hr,_,hW,hp,hn⟩ := transport_local_marking P R hr hd hR hp hn e
    let := hperf
    obtain ⟨g,hg⟩ := Atlas.G2.EvenLocal.NormalizerCover.normalizer_conjugate_le_parabolic W hW hp
    let j := (MulAut.conj g).toMonoidHom.comp B.subtype
    have hj : j.range ≤ (normalizer (W : Set _)).map (MulAut.conj g).toMonoidHom := by
      rintro _ ⟨b,rfl⟩
      exact mem_map_of_mem _ (hn b.property)
    have hq : 2 < Nat.card F := by
      rw [hF]
      have hh := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hn'
      norm_num at hh
      omega
    exact Atlas.G2.PerfectSubgroups.no_perfect_odd_rank_two_in_parabolic
      (by decide : Odd 3) hr hq j ((MulAut.conj g).injective.comp B.subtype_injective)
      (hg.imp hj.trans hj.trans)
  | triality hn' hm =>
    have hnpos : 0 < n := by omega
    obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff A n hnpos).mp hm
    obtain ⟨B,W,hperf,hr,_,hW,hp,hn⟩ := transport_local_marking P R hr hd hR hp hn e
    let := hperf
    obtain ⟨g,a,hg⟩ := Triality.Standard.TwoLocalCover.normalizer_cover n hnpos W hW hp
    let Q := Triality.Standard.Parabolics.parabolic (Triality.Standard.binaryParameters n hnpos) a
    let j := (MulAut.conj g).toMonoidHom.comp B.subtype
    have him : ∀ b, j b ∈ Q := by
      intro b
      exact hg (mem_map_of_mem _ (hn b.property))
    let f : B →* Q := j.codRestrict Q him
    have hf : Function.Injective f := fun x y h =>
      B.subtype_injective ((MulAut.conj g).injective (congrArg Subtype.val h))
    let : Group.IsPerfect f.range := Group.IsPerfect.range f
    have hd : f.range ≤ commutator Q := by
      rw [←commutator_eq_self (H := f.range)]
      exact commutator_mono le_top le_top
    let k := f.codRestrict (commutator Q) (fun x => hd ⟨x,rfl⟩)
    have hk : Function.Injective k := fun x y h => hf (congrArg Subtype.val h)
    have hb := (Theory.GroupTheory.primeRank_le_of_injective 3 k hk).trans
      (Triality.Standard.InvolutionFixedRank.derived_parabolic_threeRank_le_one
        (Triality.Standard.binaryParameters n hnpos) rfl a)
    omega
  | ree_f4 m hm _ he =>
    obtain ⟨B,W,_,_,hd,hW,hp,hn⟩ := transport_local_marking P R hr hd hR hp hn he.some
    exact ReeF4.ConverseParabolics.normalizer_fifteen_free hm W hW hp
      (hd.trans (card_dvd_of_le hn))
  | symplectic_derived _ he =>
    rw [primeRank_equiv 2 (he.some.trans
      Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix),
      (GLS3.Chapter5.PRank.alternating_hasPRank_two 6).primeRank_eq Nat.prime_two] at h2
    norm_num at h2
  | g2_derived _ he =>
    have hh := hd.trans P.card_subgroup_dvd_card
    rw [Nat.card_congr he.some.toEquiv,Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at hh
    norm_num at hh
  | tits _ he =>
    obtain ⟨B,W,_,_,hd,hW,hp,hn⟩ := transport_local_marking P R hr hd hR hp hn he.some
    exact Tits.normalizer_fifteen_free W hW hp (hd.trans (card_dvd_of_le hn))

end CFSG.Quasithin.ChapterA.Section02
