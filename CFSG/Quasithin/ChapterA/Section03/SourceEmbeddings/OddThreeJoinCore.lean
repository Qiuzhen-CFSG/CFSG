module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.OddThreeNoncentral
public import CFSG.Quasithin.ChapterA.Section01.RankActions.PerfectActions.LinearRecognition
public import Theory.GroupTheory.PGroup.ElementaryNormalizer
public import Theory.GroupTheory.PerfectSmallTwoAction
public import Theory.SpecificGroups.GL2.ThreeSolvable
public import Theory.ElementaryAbelian.Injective
public import GorensteinWalter.SL2UniversalCover
public import Theory.GroupTheory.Fitting.Equiv
public import Theory.GroupTheory.CComponent.FittingCentralizer

/-!
# Trivial two-core of the odd ternary local join

A nontrivial two-core of the component-Sylow join has a characteristic
nontrivial elementary subgroup of order at most four in the genuine ternary
carrier. The perfect component centralizes this subgroup. An involution
centralizer therefore embeds that component into prime-field SL₂, whose
nontrivial perfect subgroups are quasisimple. This contradicts the retained
nonquasisimple section. The resulting zero core discharges the ambient premise
of the defining-prime Fitting theorem on the literal join.

Source: Aschbacher--Smith A.3.21, printed pp.55--56. The involution-centralizer
and two-rank statements are the checked `RankThreeLocalStructure` clauses.
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

private theorem rankThree_elementary_card
    {G : Type*} [Group G] [Finite G] {p r : ℕ}
    (h : RankThreeLocalStructure G p r) (E : Subgroup G)
    (hE : IsElementaryAbelian 2 E) : Nat.card E ≤ 4 := by
  let := hE
  obtain ⟨S,hES⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_le_sylow
  have hsmall := (h.sylow S).2.2.1 (E.subgroupOf (S : Subgroup G))
    (IsElementaryAbelian.of_injective (subgroupOfEquivOfLe hES).toMonoidHom
      (subgroupOfEquivOfLe hES).injective)
  rwa [Nat.card_congr (subgroupOfEquivOfLe hES).toEquiv] at hsmall

private theorem rankThree_centralizer_quasisimple
    {G K : Type*} [Group G] [Finite G] [Group K] [Finite K]
    [Group.IsPerfect K] [Nontrivial K] {p r : ℕ} [Fact p.Prime]
    (ho : Odd p) (h : RankThreeLocalStructure G p r)
    (z : G) (hz : orderOf z = 2)
    (j : K →* centralizer ({z} : Set G)) (hj : Function.Injective j) :
    IsQuasisimple K := by
  obtain ⟨_,_,hs⟩ := h.involutions
  obtain ⟨_,⟨e⟩,hle⟩ := hs z hz
  let : Group.IsPerfect j.range := Group.IsPerfect.range j
  have hr : j.range ≤ primeToResidual p (centralizer ({z} : Set G)) :=
    (le_solvableResidual_of_isPerfect j.range).trans hle
  let f := e.toMonoidHom.comp (j.codRestrict _ (fun x => hr ⟨x,rfl⟩))
  exact prime_sl2_quasisimple ho f
    (e.injective.comp (fun x y hh => hj (congrArg Subtype.val hh)))

/-- The literal join has trivial two-core in an odd ternary carrier. -/
theorem rankThree_join_twoCore_eq_bot
    {A G : Type*} [Group A] [Finite A] [Group G] [Finite G]
    {p r : ℕ} [Fact p.Prime] (ho : Odd p)
    (h : RankThreeLocalStructure G p r) (f : A →* G) (hf : Function.Injective f)
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
  let g := f.comp J.subtype
  have hg : Function.Injective g := hf.comp J.subtype_injective
  have hsmall : Nat.card E ≤ 4 := by
    have he := rankThree_elementary_card h (E.map g) (IsElementaryAbelian.map g)
    rwa [Subgroup.card_map_of_injective hg] at he
  have hc : D ≤ centralizer (E : Set J) :=
    le_centralizer_of_isPerfect_of_card_le_four D E hsmall
  obtain ⟨z,hz,hzne⟩ := E.bot_or_exists_ne_one.resolve_left hEne
  have horder : orderOf z = 2 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian z hz) hzne
  let j : D →* centralizer ({g z} : Set G) :=
    (g.comp D.subtype).codRestrict _ (by
      intro d
      apply mem_centralizer_singleton_iff.mpr
      change g (d : J) * g z = g z * g (d : J)
      simpa only [map_mul] using (congrArg g (hc d.property z hz)).symm)
  have hj : Function.Injective j := fun x y hh =>
    Subtype.ext (hg (congrArg Subtype.val hh))
  have hq := rankThree_centralizer_quasisimple ho h (g z)
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

/-- A.3.21 with the required ambient core-zero hypothesis discharged on the join. -/
theorem rankThree_local_fitting_eq_defining_core
    {A G : Type*} [Group A] [Finite A] [Group G] [Finite G]
    {κ : GroupClass} (hA : IsSQTK κ A)
    {p r : ℕ} [Fact p.Prime] (ho : Odd p)
    (h : RankThreeLocalStructure G p r) (f : A →* G) (hf : Function.Injective f)
    (S : Subgroup A) {B : Subgroup A} (hB : B ∈ localCComponents S)
    (hn : ¬ IsQuasisimple B) : fittingSubgroup B = pCore p B := by
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
    exact hn (IsQuasisimple.of_mulEquiv e)
  have hcore := rankThree_join_twoCore_eq_bot ho h f hf S hB hn
  have hfit := rankThree_fitting_eq_defining_core (hA.subgroup J) hcore hB hnc h
    (f.comp (J.subtype.comp D.subtype))
    (hf.comp (J.subtype_injective.comp D.subtype_injective))
  have hm := congrArg (map e.toMonoidHom) hfit
  change (fittingSubgroup D).map e.toMonoidHom = (pCore p D).map e.toMonoidHom at hm
  rw [map_fitting_equiv e, pCore_map_iso p e] at hm
  exact hm

/-- The section form used by the original marked source pair. -/
theorem rankThree_local_core_and_fitting
    {A G : Type*} [Group A] [Finite A] [Group G] [Finite G]
    {κ : GroupClass} (hA : IsSQTK κ A)
    {p r : ℕ} [Fact p.Prime] (ho : Odd p)
    (h : RankThreeLocalStructure G p r) (f : A →* G) (hf : Function.Injective f)
    (S : Subgroup A) {B : Subgroup A} (hB : B ∈ localCComponents S)
    (hn : ¬ IsQuasisimple (B ⧸ pCore 2 B)) :
    pCore 2 (B ⊔ S : Subgroup A) = ⊥ ∧ fittingSubgroup B = pCore p B := by
  have hnB := local_not_quasisimple_of_quotient hB hn
  exact ⟨rankThree_join_twoCore_eq_bot ho h f hf S hB hnB,
    rankThree_local_fitting_eq_defining_core hA ho h f hf S hB hnB⟩

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
