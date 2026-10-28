module
public import CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape.Normal
public import Theory.GroupTheory.CyclicSylowSubnormalIndex

/-!
# Placement of the other reciprocal conjugate

The section centralizer of the original component has odd-prime rank at
most one. Cyclic Sylow transfer puts every p-generated subgroup into the
normal perfect component carrying p. The nontrivial action of the actual
reciprocal span supplies such a prime in the outside component. This places
the other H-conjugate in that component and makes its odd-rank bound exact.

Source: Aschbacher--Smith, 4.2.10(1--2), printed p.610.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape
variable {G : Type*} [Group G] [Finite G]

theorem sectionCentralizer_rank_le_one
    (hG : IsSQTK KnownSimple.IsKnownSimple G) (B : Subgroup G) [B.Normal]
    (hz : center (B ⧸ pCore 2 B) = ⊥)
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hp : p ∣ Nat.card B) :
    primeRank p (sectionCentralizer B) ≤ 1 := by
  have hc := ((le_sectionCentralizer_iff (sectionCentralizer B) B).mp le_rfl).2
  have hr := ResidualCentralizerRank.primeRank_sum_le_of_normal_factor ho
    (sectionCentralizer B) B ((commutator_mono (map_subtype_le _) le_rfl).trans hc)
    (by rw [hz]; simp)
  have hpos : 0 < primeRank p B := Nat.pos_of_ne_zero
    (fun he => PrimeRank.eq_zero_iff_not_dvd_card.mp he hp)
  have htwo := hG.stronglyQuasithin p Fact.out ho
  omega

/-- Cyclic Sylow transfer forces a p-generated actor in the section
centralizer into the normal perfect component carrying p. -/
theorem le_normal_of_prime_generated_sectionCentralizer
    (hG : IsSQTK KnownSimple.IsKnownSimple G) (B K J : Subgroup G)
    [B.Normal] [K.Normal] [Group.IsPerfect K]
    (hz : center (B ⧸ pCore 2 B) = ⊥)
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hpB : p ∣ Nat.card B)
    (hpK : p ∣ Nat.card K) (hK : K ≤ sectionCentralizer B)
    (hJ : J ≤ sectionCentralizer B) (hpJ : primeToResidual p J = ⊤) : J ≤ K := by
  let C := sectionCentralizer B
  let N := K.subgroupOf C
  let E := J.subgroupOf C
  let eK : N ≃* K := subgroupOfEquivOfLe hK
  let eJ : E ≃* J := subgroupOfEquivOfLe hJ
  let : Group.IsPerfect N := Group.IsPerfect.ofSurjective
    (f := eK.symm.toMonoidHom) eK.symm.surjective
  let P : Sylow p C := Classical.choice inferInstance
  have hr := sectionCentralizer_rank_le_one hG B hz ho hpB
  let : IsCyclic P := P.isCyclic_of_odd_of_primeRank_le_one ho hr
  have hd : p ∣ Nat.card (_root_.commutator N) := by
    rw [Group.IsPerfect.commutator_eq_top, Nat.card_congr (topEquiv : (⊤ : Subgroup N) ≃* N).toEquiv,
      Nat.card_congr eK.toEquiv]
    exact hpK
  have hi := coprime_index_of_cyclicSylow_of_dvd_commutator N P hd
  have hpE : primeToResidual p E = ⊤ := by
    have hh := map_primeToResidual (p := p) eJ.symm
    rw [hpJ,map_top_of_surjective eJ.symm.toMonoidHom eJ.symm.surjective] at hh
    exact hh.symm
  have hEN : E ≤ N := (le_primeToResidual_of_eq_top p E hpE).trans (primeToResidual_le N hi)
  intro j hj
  exact hEN (show (⟨j,hJ hj⟩ : C) ∈ E from hj)

/-- Every prime generating the moved perfect span divides the selected
component. The actual action is inner by Schreier, without assuming that
its core quotient has trivial center. -/
theorem prime_dvd_component_of_moved_span
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (K X : Subgroup G) (hK : K.IsCComponent) [K.Normal]
    [Group.IsPerfect X] [IsQuasisimple (K ⧸ pCore 2 K)]
    {p : ℕ} [Fact p.Prime] (hpX : primeToResidual p X = ⊤)
    (hmoved : ¬ ⁅X,K⁆ ≤ pCore 2 G) : p ∣ Nat.card K := by
  let a : X →* MulAut (K ⧸ pCore 2 K) :=
    ((quotientAut (pCore 2 K)).comp MulAut.conjNormal).comp X.subtype
  have ha : a.range ≠ ⊥ := by
    intro he
    apply hmoved
    apply le_trans ?_ (pCoreIn_le_of_subnormal 2 hK.subnormal)
    apply commutator_le.mpr
    intro x hx k hk
    have hax : a ⟨x,hx⟩ = 1 := mem_bot.mp (he ▸ (show a ⟨x,hx⟩ ∈ a.range from ⟨_,rfl⟩))
    have hfix := DFunLike.congr_fun hax (QuotientGroup.mk' (pCore 2 K) ⟨k,hk⟩)
    simp only [a,MonoidHom.comp_apply,quotientAut_apply_mk,MulAut.one_apply] at hfix
    have hq := QuotientGroup.eq_iff_div_mem.mp hfix
    refine ⟨(MulAut.conjNormal x (⟨k,hk⟩ : K)) / ⟨k,hk⟩,hq,?_⟩
    simp [div_eq_mul_inv,commutatorElement_def]
  let : Group.IsSolvable (MulAut.Outer (K ⧸ pCore 2 K)) :=
    ChapterA.Section03.SourceComponents.quasisimple_section_outer_solvable hG
      (ChapterA.Section02.IsSectionOf.quotient_subgroup K (pCore 2 K))
  let : Group.IsPerfect a.range := Group.IsPerfect.range a
  have hpA : p ∣ Nat.card a.range := by
    by_contra hnot
    have hker := primeToResidual_le_ker a.rangeRestrict
      ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hnot)
    apply ha
    apply MonoidHom.range_eq_bot_iff.mpr
    apply MonoidHom.ext
    intro x
    exact congrArg Subtype.val (show a.rangeRestrict x = 1 from hker (hpX ▸ mem_top x))
  have hi := MulAut.perfect_subgroup_le_inner a.range
  exact ((hpA.trans (card_dvd_of_le hi)).trans
    (card_dvd_of_surjective (MulAut.conj : (K ⧸ pCore 2 K) →* MulAut (K ⧸ pCore 2 K)).rangeRestrict
      (MonoidHom.rangeRestrict_surjective _))).trans
    (card_dvd_of_surjective (QuotientGroup.mk' (pCore 2 K)) (QuotientGroup.mk'_surjective _))

private theorem quotient_sqtk (hG : IsSQTK KnownSimple.IsKnownSimple G) :
    IsSQTK KnownSimple.IsKnownSimple (G ⧸ pCore 2 G) := by
  refine ⟨?_,hG.isKGroup.quotient _⟩
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
    (hG.stronglyQuasithin p hp ho)

/-- A perfect group with centerless quasisimple two-core quotient is
p-generated for every prime in that quotient. -/
theorem primeToResidual_eq_top_of_centerless_core_quotient
    (L : Subgroup G) [Group.IsPerfect L] [IsQuasisimple (L ⧸ pCore 2 L)]
    (hz : center (L ⧸ pCore 2 L) = ⊥) {p : ℕ} [Fact p.Prime]
    (hp : p ∣ Nat.card (L ⧸ pCore 2 L)) : primeToResidual p L = ⊤ := by
  let : IsSimpleGroup ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) := IsQuasisimple.simple
  let : IsSimpleGroup (L ⧸ pCore 2 L) :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.isSimpleGroup
  have hperfect : IsPPerfect 2 L := by
    intro N hN hquot
    let := hN
    have hs : Subsingleton (L ⧸ N) := by
      by_contra! hn
      exact Group.IsPerfect.not_isNilpotent (L ⧸ N) hquot.isNilpotent
    apply eq_top_iff.mpr
    intro l _
    exact (QuotientGroup.eq_one_iff l).mp (Subsingleton.elim _ _)
  exact primeToResidual_eq_top_of_simple_quotient p 2 (pCore 2 L)
    pCore_isPGroup hperfect hp

/-- Source 4.2.10(1): the actual other H-conjugate lies in the same outside
component selected by reciprocity. Cyclic Sylow transfer is performed in
the literal section centralizer inside M. -/
theorem reciprocal_conjugate_le_component {L H : Subgroup G}
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hM : IsSQTK KnownSimple.IsKnownSimple (normalizer (L : Set G)))
    (hd : ReciprocalData L H) [Group.IsPerfect L] [IsQuasisimple (L ⧸ pCore 2 L)]
    (K : Subgroup (normalizer (L : Set G))) (hK : K.IsCComponent)
    [K.Normal] [IsQuasisimple (K ⧸ pCore 2 K)]
    (hout : ¬ K ≤ H.subgroupOf (normalizer (L : Set G)))
    (hmoved : ¬ ⁅(conjugateSpanBy L H).subgroupOf (normalizer (L : Set G)),K⁆ ≤
      pCore 2 (normalizer (L : Set G)))
    (t : H) (ht : (t : G) ∉ normalizer (L : Set G)) :
    L.map (MulAut.conj (t : G)).toMonoidHom ≤ K.map (normalizer (L : Set G)).subtype := by
  let M := normalizer (L : Set G)
  let B := L.subgroupOf M
  let J := L.map (MulAut.conj (t : G)).toMonoidHom
  let X := (conjugateSpanBy L H).subgroupOf M
  have hLH : L ≤ H := hd.1 ▸ (map_subtype_le _).trans inf_le_right
  let a : (L.subgroupOf H) ≃* L := subgroupOfEquivOfLe hLH
  let b : B ≃* L := subgroupOfEquivOfLe L.le_normalizer
  have htL : (⊤ : Subgroup L).IsCComponent := by
    simpa only [subgroupOf_self,map_top_of_surjective a.toMonoidHom a.surjective]
      using (hd.2.1.subgroupOf le_rfl).map_equiv a
  have htB : (⊤ : Subgroup B).IsCComponent := by
    simpa only [map_top_of_surjective b.symm.toMonoidHom b.symm.surjective]
      using htL.map_equiv b.symm
  let : B.Normal := (normal_subgroupOf_iff_le_normalizer L.le_normalizer).mpr le_rfl
  have hB : B.IsCComponent := by
    simpa only [←MonoidHom.range_eq_map,range_subtype]
      using htB.map_subtype (inferInstance : B.Normal).isSubnormal
  have hne : K ≠ B := fun he => hout (he ▸ comap_mono hLH)
  have hz := reciprocal_coreQuotient_center_eq_bot hH hd
  let qb := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  have hzB : center (B ⧸ pCore 2 B) = ⊥ := by
    apply (eq_bot_iff_card _).mpr
    rw [Nat.card_congr (centerCongr qb).toEquiv,hz]
    exact Nat.card_unique
  have hJX : J ≤ conjugateSpanBy L H := by
    rintro _ ⟨l,hl,rfl⟩
    exact subset_closure ⟨(t : G),t.property,l,hl,rfl⟩
  have hJM : J ≤ M := hJX.trans (hd.2.2.2.2.1.trans inf_le_right)
  let A := L.subgroupOf H
  let E := A.map (MulAut.conj t).toMonoidHom
  have hE : E.IsCComponent := hd.2.1.map_equiv (MulAut.conj t)
  have hEA : E ≠ A := by
    intro he
    have htN := mem_normalizer_iff_map_conj_eq.mpr he
    rw [hd.2.2.1] at htN
    exact ht htN
  have hmap : E.map H.subtype = J := by
    rw [map_map]
    rw [show H.subtype.comp (MulAut.conj t).toMonoidHom =
      (MulAut.conj (t : G)).toMonoidHom.comp H.subtype from rfl,←map_map,
      map_subgroupOf_eq_of_le hLH]
  have hcH := (Chapter1.Section02.proposition_1_2_1_two_of_A_3_7
    (fun Y _ _ => ChapterA.Section03.CComponentCommutation.universal_A_3_7 Y)
    (quotient_sqtk hH) hE hd.2.1 hEA).1.trans inf_le_right
  have hcG : ⁅J,L⁆ ≤ L.pCoreIn 2 := by
    have hh := map_mono (f := H.subtype) hcH
    rwa [map_commutator,hmap,map_subgroupOf_eq_of_le hLH,
      map_pCoreIn_of_injective 2 _ _ H.subtype_injective,map_subgroupOf_eq_of_le hLH] at hh
  have hJC : J.subgroupOf M ≤ sectionCentralizer B := by
    apply (le_sectionCentralizer_iff _ _).mpr
    refine ⟨le_normalizer_of_normal,?_⟩
    apply (map_le_map_iff_of_injective M.subtype_injective).mp
    have hbmap : B.map M.subtype = L :=
      map_subgroupOf_eq_of_le (show L ≤ M from L.le_normalizer)
    rw [map_commutator,map_pCoreIn_of_injective 2 _ _ M.subtype_injective,
      map_subgroupOf_eq_of_le hJM,hbmap]
    exact hcG
  have hKC : K ≤ sectionCentralizer B :=
    (le_sectionCentralizer_iff _ _).mpr ⟨le_normalizer_of_normal,
      (Chapter1.Section02.proposition_1_2_1_two_of_A_3_7
        (fun Y _ _ => ChapterA.Section03.CComponentCommutation.universal_A_3_7 Y)
        (quotient_sqtk hM) hK hB hne).1.trans inf_le_right⟩
  let : IsSimpleGroup ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) := IsQuasisimple.simple
  let : IsSimpleGroup (L ⧸ pCore 2 L) :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.isSimpleGroup
  obtain ⟨p,hp,ho,_,hdiv⟩ := Perfect.exists_odd_prime_ne_dvd_card (L ⧸ pCore 2 L) Nat.prime_two
  let : Fact p.Prime := ⟨hp⟩
  have hpL := primeToResidual_eq_top_of_centerless_core_quotient L hz hdiv
  let x := subgroupOfEquivOfLe (hd.2.2.2.2.1.trans inf_le_right)
  let : Group.IsPerfect (conjugateSpanBy L H) := conjugateSpanBy_isPerfect L H
  let : Group.IsPerfect X := Group.IsPerfect.ofSurjective
    (f := x.symm.toMonoidHom) x.symm.surjective
  have hpX : primeToResidual p X = ⊤ := by
    have hh := map_primeToResidual (p := p) x.symm
    rw [primeToResidual_span_eq_top p L H hpL,
      map_top_of_surjective x.symm.toMonoidHom x.symm.surjective] at hh
    exact hh.symm
  have hpK := prime_dvd_component_of_moved_span hM K X hK hpX hmoved
  have hpB : p ∣ Nat.card B := by
    rw [Nat.card_congr b.toEquiv]
    exact hdiv.trans (card_dvd_of_surjective (QuotientGroup.mk' (pCore 2 L))
      (QuotientGroup.mk'_surjective _))
  let ej : L ≃* J.subgroupOf M :=
    (L.equivMapOfInjective (MulAut.conj (t : G)).toMonoidHom
      (MulAut.conj (t : G)).injective).trans (subgroupOfEquivOfLe hJM).symm
  have hpJ : primeToResidual p (J.subgroupOf M) = ⊤ := by
    have hh := map_primeToResidual (p := p) ej
    rw [hpL,map_top_of_surjective ej.toMonoidHom ej.surjective] at hh
    exact hh.symm
  let : Group.IsPerfect K := hK.perfect
  have hjk := le_normal_of_prime_generated_sectionCentralizer hM B K (J.subgroupOf M)
    hzB ho hpB hpK hKC hJC hpJ
  have hh := map_mono (f := M.subtype) hjk
  rwa [map_subgroupOf_eq_of_le hJM] at hh

/-- The source rank assertion is equality: the other conjugate already
lies in K and has the original component's order. -/
theorem reciprocal_component_odd_rank_eq_one {L H : Subgroup G}
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hM : IsSQTK KnownSimple.IsKnownSimple (normalizer (L : Set G)))
    (hd : ReciprocalData L H) [Group.IsPerfect L] [IsQuasisimple (L ⧸ pCore 2 L)]
    (K : Subgroup (normalizer (L : Set G))) (hK : K.IsCComponent)
    [K.Normal] [IsQuasisimple (K ⧸ pCore 2 K)]
    (hout : ¬ K ≤ H.subgroupOf (normalizer (L : Set G)))
    (hmoved : ¬ ⁅(conjugateSpanBy L H).subgroupOf (normalizer (L : Set G)),K⁆ ≤
      pCore 2 (normalizer (L : Set G))) :
    ∀ p : ℕ, p.Prime → Odd p → p ∣ Nat.card L → primeRank p K = 1 := by
  have hn : ¬ H ≤ normalizer (L : Set G) := by
    intro hh
    have he := subgroupOf_eq_top.mpr hh
    have hi := hd.2.2.2.1
    rw [he,index_top] at hi
    norm_num at hi
  obtain ⟨t,htH,htN⟩ := SetLike.not_le_iff_exists.mp hn
  have hle := reciprocal_conjugate_le_component hH hM hd K hK hout hmoved ⟨t,htH⟩ htN
  intro p hp ho hdiv
  let : Fact p.Prime := ⟨hp⟩
  have hpJ : p ∣ Nat.card (L.map (MulAut.conj t).toMonoidHom) := by
    rwa [card_map_of_injective (MulAut.conj t).injective]
  have hpK := hpJ.trans (card_dvd_of_le hle)
  rw [card_map_of_injective (normalizer (L : Set G)).subtype_injective] at hpK
  have hpos : 0 < primeRank p K := Nat.pos_of_ne_zero
    (fun he => PrimeRank.eq_zero_iff_not_dvd_card.mp he hpK)
  have hbound := reciprocal_component_odd_rank hH hM hd K hK hout p hp ho hdiv
  omega

omit [Finite G] in
/-- The same index-two intersection normalizes both actual H-conjugates. -/
theorem reciprocal_conjugate_normalizer {L H : Subgroup G}
    (hd : ReciprocalData L H) (t : H) :
    H ⊓ normalizer (L : Set G) ≤
      normalizer (L.map (MulAut.conj (t : G)).toMonoidHom : Set G) := by
  let M := normalizer (L : Set G)
  let A := L.subgroupOf H
  let E := A.map (MulAut.conj t).toMonoidHom
  have hLH : L ≤ H := hd.1 ▸ (map_subtype_le _).trans inf_le_right
  have hmap : E.map H.subtype = L.map (MulAut.conj (t : G)).toMonoidHom := by
    rw [map_map]
    rw [show H.subtype.comp (MulAut.conj t).toMonoidHom =
      (MulAut.conj (t : G)).toMonoidHom.comp H.subtype from rfl,←map_map,
      map_subgroupOf_eq_of_le hLH]
  let : (M.subgroupOf H).Normal := normal_of_index_eq_two hd.2.2.2.1
  have hn : normalizer (E : Set H) = M.subgroupOf H := by
    rw [←map_equiv_normalizer_eq A (MulAut.conj t),hd.2.2.1]
    exact mem_normalizer_iff_map_conj_eq.mp (le_normalizer_of_normal (mem_top t))
  have hh := E.le_normalizer_map H.subtype
  rw [hn,hmap,subgroupOf_map_subtype] at hh
  simpa only [inf_comm] using hh

end CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape
