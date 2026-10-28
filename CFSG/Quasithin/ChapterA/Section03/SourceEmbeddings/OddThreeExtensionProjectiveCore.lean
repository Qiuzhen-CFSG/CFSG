module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.OddThreeExtensionCovers
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.OddThreeJoinCore
public import Theory.GroupTheory.PrimeRankElementary

/-!
# Odd ternary joins through cubic central covers

The actual component and its SQTK hypothesis remain downstairs. Elementary
subgroups in its two-core have order at most four by the projective rank
bound. Its perfect component then centralizes an involution and embeds in
the genuine SL₂ residual through the cubic kernel. Odd cross-characteristic
cores lift to the special carrier only for the automizer centralization;
this identifies the original component's Fitting subgroup downstairs.

Source: Aschbacher--Smith A.3.21, printed pp.55--56.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings

private theorem prime_sl2_quasisimple
    {K : Type*} [Group K] [Finite K] [Group.IsPerfect K] [Nontrivial K]
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (f : K →* SL(2,ZMod p)) (hf : Function.Injective f) : IsQuasisimple K := by
  have hp := (Fact.out : p.Prime)
  have hlarge : 3 < p := by
    by_contra hn
    have he : p = 3 := by have := hp.two_le; have := Nat.odd_iff.mp ho; omega
    subst p
    let : Group.IsSolvable (GL (Fin 2) (ZMod 3)) := Matrix.GeneralLinearGroup.three_isSolvable
    let : Group.IsSolvable SL(2,ZMod 3) := Group.isSolvable_of_isSolvable_injective
      (Matrix.SpecialLinearGroup.toGL_injective (n := Fin 2) (R := ZMod 3))
    exact Group.IsPerfect.not_isSolvable K (Group.isSolvable_of_isSolvable_injective hf)
  let e : K ≃* f.range := MonoidHom.ofInjective hf
  let : Group.IsPerfect f.range := Group.IsPerfect.ofSurjective
    (f := e.toMonoidHom) e.surjective
  let : Nontrivial f.range := e.symm.nontrivial
  rcases ChapterA.RankActions.primePerfectSL2Recognition p hlarge f.range
      inferInstance inferInstance with hh | ⟨_,hh⟩
  · obtain ⟨a⟩ := hh
    let : Fact (3 < Nat.card (ZMod p)) := ⟨by simpa using hlarge⟩
    exact IsQuasisimple.of_mulEquiv (e.trans a).symm
  · obtain ⟨a⟩ := hh
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    let : Fact (3 < Nat.card (ZMod 5)) := ⟨by norm_num⟩
    exact IsQuasisimple.of_mulEquiv (e.trans a).symm

private theorem cubic_centralizer_quasisimple
    {G H K : Type*} [Group G] [Finite G] [Group H] [Finite H]
    [Group K] [Finite K] [Group.IsPerfect K] [Nontrivial K]
    {q residue : ℕ} [Fact q.Prime] (ho : Odd q)
    (h : RankThreeLocalStructure H q residue)
    (f : H →* G) (hf : Function.Surjective f) (hc : f.ker ≤ center H)
    (h3 : ∀ x ∈ f.ker, x ^ 3 = 1)
    (z : G) (hz : orderOf z = 2)
    (j : K →* centralizer ({z} : Set G)) (hj : Function.Injective j) :
    IsQuasisimple K := by
  let a := (centralizer ({z} : Set G)).subtype.comp j
  let : Group.IsPerfect a.range := Group.IsPerfect.range a
  have hAz : a.range ≤ centralizer ({z} : Set G) := by
    rintro x ⟨k,rfl⟩
    exact (j k).property
  obtain ⟨i,hi⟩ := rankThree_cubic_quotient_perfect_embedding h f hf hc h3 z hz a.range hAz
  exact prime_sl2_quasisimple ho (i.comp a.rangeRestrict)
    (hi.comp (by
      intro x y hh
      apply hj
      apply Subtype.ext
      have hh' : a x = a y := congrArg (fun t : a.range => (t : G)) hh
      exact hh'))

/-- The literal join has trivial two-core in an odd ternary carrier. -/
theorem rankThree_cubic_join_twoCore_eq_bot
    {A G : Type*} [Group A] [Finite A] [Group G] [Finite G]
    {p r : ℕ} [Fact p.Prime] (ho : Odd p)
    (h : RankThreeLocalStructure G p r)
    (f : G →* A) (hf : Function.Surjective f) (hfc : f.ker ≤ center G)
    (hf3 : ∀ x ∈ f.ker, x ^ 3 = 1) (hrank : primeRank 2 A ≤ 2)
    (S : Subgroup A) {B : Subgroup A} (hB : B ∈ localCComponents S)
    (hn : ¬ IsQuasisimple B) : pCore 2 (B ⊔ S : Subgroup A) = ⊥ := by
  let J := B ⊔ S
  let D := B.subgroupOf J
  let e : D ≃* B := subgroupOfEquivOfLe le_sup_left
  let : Group.IsPerfect D := hB.perfect
  let : Nontrivial D := (nontrivial_iff_ne_bot D).mpr hB.ne_bot
  by_contra hcore
  obtain ⟨E,hEne,_,hE,hNE⟩ := exists_nontrivial_elementary_with_normalizer_le
    (pCore 2 J) pCore_isPGroup hcore
  let : IsElementaryAbelian 2 E := hE
  have hnormal : (⊤ : Subgroup J) ≤ normalizer (E : Set J) := by
    rw [← (pCore 2 J).normalizer_eq_top]
    exact hNE
  let : E.Normal := (normalizer_eq_top_iff).mp (top_unique hnormal)
  let g := J.subtype
  have hg : Function.Injective g := J.subtype_injective
  have hsmall : Nat.card E ≤ 4 := by
    have he := (primeRank_le_iff_elementary_card_le A).mp hrank
      (E.map g) (IsElementaryAbelian.map g)
    rwa [Subgroup.card_map_of_injective hg] at he
  have hc : D ≤ centralizer (E : Set J) :=
    le_centralizer_of_isPerfect_of_card_le_four D E hsmall
  obtain ⟨z,hz,hzne⟩ := E.bot_or_exists_ne_one.resolve_left hEne
  have horder : orderOf z = 2 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian z hz) hzne
  let j : D →* centralizer ({g z} : Set A) :=
    (g.comp D.subtype).codRestrict _ (by
      intro d
      apply mem_centralizer_singleton_iff.mpr
      change g (d : J) * g z = g z * g (d : J)
      simpa only [map_mul] using (congrArg g (hc d.property z hz)).symm)
  have hj : Function.Injective j := by
    intro x y hh
    apply Subtype.ext
    apply hg
    have hh' : g (x : J) = g (y : J) :=
      congrArg (fun t : centralizer ({g z} : Set A) => (t : A)) hh
    exact hh'
  have hq := cubic_centralizer_quasisimple ho h f hf hfc hf3 (g z)
    ((orderOf_injective g hg z).trans horder) j hj
  let := hq
  exact hn (IsQuasisimple.of_mulEquiv e)

private theorem local_not_quasisimple_of_quotient
    {A : Type*} [Group A] [Finite A] {S B : Subgroup A}
    (hB : B ∈ localCComponents S) (hn : ¬ IsQuasisimple (B ⧸ pCore 2 B)) :
    ¬ IsQuasisimple B := by
  intro hq
  let := hq
  have htop : (⊤ : Subgroup B).IsCComponent := by
    simpa only [subgroupOf_self] using
      hB.subgroupOf_of_le (show B ≤ B from le_rfl) (show B ≤ B ⊔ S from le_sup_left)
  let := pCore_isNilpotent (p := 2) (G := B)
  have hbar := htop.map_quotient (pCore 2 B)
  rw [map_top_of_surjective _ (QuotientGroup.mk'_surjective (pCore 2 B))] at hbar
  let : Nontrivial (⊤ : Subgroup (B ⧸ pCore 2 B)) :=
    (nontrivial_iff_ne_bot _).mpr hbar.ne_bot
  let : Nontrivial (B ⧸ pCore 2 B) := (topEquiv (G := B ⧸ pCore 2 B)).injective.nontrivial
  exact hn (IsQuasisimple.of_surjective (QuotientGroup.mk' (pCore 2 B))
    (QuotientGroup.mk'_surjective (pCore 2 B)))

theorem rankThree_cubic_fitting_eq_defining_core
    {A H : Type*} [Group A] [Finite A] [Group H] [Finite H]
    {κ : GroupClass} (hA : IsSQTK κ A) (hO : pCore 2 A = ⊥)
    {B : Subgroup A} (hB : B.IsCComponent) (hn : ¬ fittingSubgroup B ≤ center B)
    {q residue : ℕ} [Fact q.Prime] (h : RankThreeLocalStructure H q residue)
    (f : H →* A) (hf : Function.Surjective f) (hc : f.ker ≤ center H) :
    fittingSubgroup B = pCore q B := by
  let : Group.IsPerfect B := hB.perfect
  have hquot := NoncentralFitting.primeSL2FittingQuotient_of_noncentral
    RankActions.primeSL2CoverRigidity hA hO hB hn
  apply NoncentralFitting.CoreShapes.fitting_eq_core_of_support
  intro r hr hd
  let : Fact r.Prime := ⟨hr⟩
  by_contra hne
  have ho : Odd r := (NoncentralFitting.fitting_odd_card hB hO).of_dvd_nat hd
  let Q := (pCore r B).map B.subtype
  have hBQ : B ≤ normalizer (Q : Set A) := by
    have hh := map_mono (f := B.subtype)
      (show (⊤ : Subgroup B) ≤ normalizer (pCore r B : Set B) by
        rw [(pCore r B).normalizer_eq_top])
    rw [←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh.trans ((pCore r B).le_normalizer_map B.subtype)
  have hcentral := rankThree_central_quotient_centralizes_odd_core h f hf hc ho hne
    B Q (pCore_isPGroup.map B.subtype) hBQ
  apply NoncentralFitting.CoreShapes.core_not_central_of_dvd
    RankActions.primeSL2CoverRigidity hB hquot hd
  intro b hb
  apply mem_center_iff.mpr
  intro a
  exact Subtype.ext ((hcentral a.property b (mem_map_of_mem B.subtype hb)).symm)

theorem rankThree_cubic_local_core_and_fitting
    {A H : Type*} [Group A] [Finite A] [Group H] [Finite H]
    {κ : GroupClass} (hA : IsSQTK κ A)
    {q residue : ℕ} [Fact q.Prime] (ho : Odd q)
    (h : RankThreeLocalStructure H q residue)
    (f : H →* A) (hf : Function.Surjective f) (hc : f.ker ≤ center H)
    (h3 : ∀ x ∈ f.ker, x ^ 3 = 1) (hrank : primeRank 2 A ≤ 2)
    (S : Subgroup A) {B : Subgroup A} (hB : B ∈ localCComponents S)
    (hn : ¬ IsQuasisimple (B ⧸ pCore 2 B)) :
    pCore 2 (B ⊔ S : Subgroup A) = ⊥ ∧ fittingSubgroup B = pCore q B := by
  have hnB := local_not_quasisimple_of_quotient hB hn
  have hcore := rankThree_cubic_join_twoCore_eq_bot ho h f hf hc h3 hrank S hB hnB
  refine ⟨hcore,?_⟩
  let J := B ⊔ S
  let D := B.subgroupOf J
  let e : D ≃* B := subgroupOfEquivOfLe le_sup_left
  have hnc : ¬ fittingSubgroup D ≤ center D := by
    intro hh
    have hr : solvableRadical D = center D := by
      apply le_antisymm (solvableRadical_le_center_of_fitting_le_center hh)
      exact le_solvableRadical (center D) inferInstance
        (Group.isSolvable_of_comm (fun a b => Subtype.ext
          (mem_center_iff.mp a.property b).symm))
    let := hB.perfect
    let := hB.isSimpleGroup_quotient_solvableRadical
    let : IsQuasisimple D := ⟨(QuotientGroup.quotientMulEquivOfEq hr).symm.isSimpleGroup⟩
    exact hnB (IsQuasisimple.of_mulEquiv e)
  -- Work in the original join; only prime-subgroups lift to the carrier.
  have hfit : fittingSubgroup D = pCore q D := by
    let : Group.IsPerfect D := hB.perfect
    have hquot := NoncentralFitting.primeSL2FittingQuotient_of_noncentral
      RankActions.primeSL2CoverRigidity (hA.subgroup J) hcore hB hnc
    apply NoncentralFitting.CoreShapes.fitting_eq_core_of_support
    intro r hr hd
    let : Fact r.Prime := ⟨hr⟩
    by_contra hne
    have hor : Odd r := (NoncentralFitting.fitting_odd_card hB hcore).of_dvd_nat hd
    let i := J.subtype.comp D.subtype
    let Q := (pCore r D).map i
    let K := i.range
    let : Group.IsPerfect K := Group.IsPerfect.range i
    have hKQ : K ≤ normalizer (Q : Set A) := by
      change i.range ≤ normalizer (Q : Set A)
      rw [MonoidHom.range_eq_map]
      exact (map_mono (show (⊤ : Subgroup D) ≤ normalizer (pCore r D : Set D) by
        rw [(pCore r D).normalizer_eq_top])).trans ((pCore r D).le_normalizer_map i)
    have hz := rankThree_central_quotient_centralizes_odd_core h f hf hc hor hne
      K Q (pCore_isPGroup.map i) hKQ
    apply NoncentralFitting.CoreShapes.core_not_central_of_dvd
      RankActions.primeSL2CoverRigidity hB hquot hd
    intro b hb
    apply mem_center_iff.mpr
    intro a
    exact Subtype.ext (Subtype.ext ((hz ⟨a,rfl⟩ (i b) (mem_map_of_mem i hb)).symm))
  have hm := congrArg (map e.toMonoidHom) hfit
  rw [map_fitting_equiv e,pCore_map_iso q e] at hm
  exact hm

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
