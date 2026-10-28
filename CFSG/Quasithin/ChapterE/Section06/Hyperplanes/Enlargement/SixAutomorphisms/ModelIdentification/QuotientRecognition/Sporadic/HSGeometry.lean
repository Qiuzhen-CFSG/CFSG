module
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.SixSylowFixer.Transport
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.Source
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.DerivedCentralizer
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismTwoRank
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.RankTwo.Action
/-!
# The HS actors forced by the fixed-six enlargement

The distinguished involution has an A₆ component, so its actual HS class is
the noncentral product class. An elementary actor group of order eight has
an inner actor outside its distinguished involution, since Out(HS) has order
at most two. The marked component-Sylow calculation produces a central-class
actor. Its derived fixed group has order 3840, whereas the distinguished
fixed group has order 2880. All actor and component markings are retained.

Source: Aschbacher–Smith E.6.23, p.254, and 16.1.5(10), p.1172.
-/
public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.Sporadic.HSGeometry
open _root_.Sporadic.LeechRelated.HS
open Chapter16.OtherPreliminaries.JankoTwoHigmanSims
open HSInner.ClassCoverage HSInner.ClassCoverage.ProductEmbedding
open HSInner.ClassCoverage.ProductEmbedding.SylowFixerCertificate
open RankTwo
variable [IsSimpleGroup Carrier] [Group.IsPerfect Carrier]

theorem exists_inner_outside (A : Subgroup (MulAut Carrier)) (hA : Nat.card A = 8) :
    ∃ x : Carrier, MulAut.conj x ∈ A ∧ x ≠ 1 ∧ x ≠ t := by
  classical
  by_contra h
  have hc (x : Carrier) (hx : MulAut.conj x ∈ A) : x = 1 ∨ x = t := by
    by_cases h1 : x = 1
    · exact Or.inl h1
    by_cases ht : x = t
    · exact Or.inr ht
    exact (h ⟨x,hx,h1,ht⟩).elim
  let f := (QuotientGroup.mk' (MulAut.innerSubgroup Carrier)).comp A.subtype
  have hk : f.ker.map A.subtype ≤ zpowers (MulAut.conj t) := by
    rintro a ⟨b,hb,rfl⟩
    have hm : (b : MulAut Carrier) ∈ MulAut.innerSubgroup Carrier :=
      (QuotientGroup.eq_one_iff _).mp (show f b = 1 from hb)
    obtain ⟨x,hx⟩ := hm
    rcases hc x (hx.symm ▸ b.property) with rfl | rfl
    · have he : A.subtype b = MulAut.conj 1 := hx.symm
      rw [he, map_one]
      exact one_mem _
    · exact hx ▸ mem_zpowers _
  have hker : Nat.card f.ker ≤ 2 := by
    calc
      Nat.card f.ker = Nat.card (f.ker.map A.subtype) :=
        (card_map_of_injective A.subtype_injective).symm
      _ ≤ Nat.card (zpowers (MulAut.conj t)) :=
        Nat.card_le_card_of_injective _ (inclusion_injective hk)
      _ = 2 := by rw [Nat.card_zpowers, orderOf_injective _ HSInner.conj_injective, t_order]
  have hrange : Nat.card f.range ≤ 2 :=
    f.range.card_le_card_group.trans (Nat.le_of_dvd (by decide) outer_card_dvd_two)
  have hp := f.ker.card_mul_index
  rw [index_ker,hA] at hp
  nlinarith

theorem exists_central_actor_of_t (s : FixedSixAction Carrier)
    (hs : s.involution = MulAut.conj t) :
    ∃ x : Carrier, IsConj EvenLocalCandidates.e0 x ∧ MulAut.conj x ∈ s.actors := by
  let := s.elementary
  obtain ⟨x,hx,hx1,hxt⟩ := exists_inner_outside s.actors s.card_actors
  have hx2 : orderOf x = 2 := by
    apply orderOf_eq_prime _ hx1
    apply HSInner.conj_injective
    rw [map_pow,map_one]
    exact elemPow_eq_one_of_isElementaryAbelian (MulAut.conj x) hx
  have hxtcomm : Commute x t := by
    apply Commute.of_map HSInner.conj_injective
    have hh := congrArg Subtype.val (mul_comm
      (⟨MulAut.conj x,hx⟩ : s.actors) ⟨s.involution,s.involution_mem⟩)
    change MulAut.conj x * s.involution = s.involution * MulAut.conj x at hh
    rw [hs] at hh
    exact hh
  have hC : IsComponentIn s.six (centralizer ({t} : Set Carrier)) := by
    simpa only [hs,MulAut.fixedSubgroup_conj] using s.component
  have hD : s.six = D := component_eq_D s.six hC
  let e := MulEquiv.subgroupCongr hD
  let P := s.sylow.mapSurjective (f := e.toMonoidHom) e.surjective
  have hf : ∀ y ∈ (P : Subgroup D), Commute x (y : Carrier) := by
    rintro y ⟨z,hz,rfl⟩
    exact mul_inv_eq_iff_eq_mul.mp (s.fixes (MulAut.conj x) hx z hz)
  rcases sylow_fixer_central_class P x
    (mem_centralizer_singleton_iff.mpr hxtcomm.eq) hf hx2 hxt with hc | hc
  · exact ⟨x,hc,hx⟩
  · refine ⟨x*t,hc,?_⟩
    rw [map_mul]
    exact s.actors.mul_mem hx (hs ▸ s.involution_mem)


theorem involution_compatible_t (s : FixedSixAction Carrier) :
    ∃ e : MulAut Carrier, MulAut.congr e s.involution = MulAut.conj t := by
  have hi : ∃ x, s.involution = MulAut.conj x := by
    by_contra ho
    obtain ⟨e⟩ := HSOuter.outer_component_equiv s.involution s.involution_order ho
      (s.six.subgroupOf s.involution.fixedSubgroup) s.component.2
    obtain ⟨f⟩ := s.model
    have he := Nat.card_congr ((subgroupOfEquivOfLe s.component.1).symm.trans e).toEquiv
    rw [Nat.card_congr f.toEquiv] at he
    change Nat.card (alternatingGroup (Fin 6)) = Nat.card (alternatingGroup (Fin 8)) at he
    rw [nat_card_alternatingGroup,nat_card_alternatingGroup] at he
    norm_num at he
  obtain ⟨x,hx⟩ := hi
  have ho : orderOf x = 2 :=
    (orderOf_injective MulAut.conj HSInner.conj_injective x).symm.trans
      (hx ▸ s.involution_order)
  rcases involution_classes x ho with hcentral | ht
  · obtain ⟨e⟩ := HSInner.fixed_equiv_centralizer_of_isConj hcentral
    have he : s.involution.fixedSubgroup ≃* centralizer ({EvenLocalCandidates.e0} : Set Carrier) := by
      rw [hx]
      exact e
    exact ((HSInner.selfCentralizing_transport he.symm
      HSInner.centralizer_selfCentralizing).not_isComponent _ s.component.2).elim
  · obtain ⟨k,hk⟩ := isConj_iff.mp ht
    refine ⟨MulAut.conj k⁻¹,?_⟩
    rw [hx,MulAut.congr_conj]
    congr 1
    change k⁻¹*x*k = t
    rw [← hk]
    group

omit [IsSimpleGroup Carrier] [Group.IsPerfect Carrier] in
private theorem derived_card_congr {D E : Type*} [Group D] [Group E]
    (e : D ≃* E) : Nat.card (commutator D) = Nat.card (commutator E) := by
  have he : (commutator D).map e.toMonoidHom = commutator E := by
    rw [map_commutator_eq,MonoidHom.range_eq_top.mpr e.surjective,← commutator_def]
  have hc := card_map_of_injective (f := e.toMonoidHom) (K := commutator D) e.injective
  rw [he] at hc
  exact hc.symm

omit [IsSimpleGroup Carrier] [Group.IsPerfect Carrier] in
theorem central_class_derived_card (x : Carrier) (hx : IsConj EvenLocalCandidates.e0 x) :
    Nat.card (commutator (MulAut.conj x).fixedSubgroup) = 3840 := by
  obtain ⟨e⟩ := HSInner.fixed_equiv_centralizer_of_isConj hx
  exact (derived_card_congr e).trans HSInner.DerivedCentralizer.centralizer_derived_card

theorem exists_actor_derived_card (s : FixedSixAction Carrier) :
    Nat.card s.involution.fixedSubgroup = 2880 ∧
      ∃ a : MulAut Carrier, a ∈ s.actors ∧ a ≠ 1 ∧
        Nat.card (commutator a.fixedSubgroup) = 3840 := by
  obtain ⟨e,he⟩ := involution_compatible_t s
  have hs : (s.map e).involution = MulAut.conj t := he
  have hcard : Nat.card s.involution.fixedSubgroup = 2880 := by
    have hc := Nat.card_congr (MulAut.fixedSubgroupCongr e s.involution).toEquiv
    rw [he,MulAut.fixedSubgroup_conj] at hc
    obtain ⟨q⟩ := product_centralizer_equiv
    exact hc.trans ((Nat.card_congr q.toEquiv).trans product_card)
  obtain ⟨x,hx,hmem⟩ := exists_central_actor_of_t (s.map e) hs
  obtain ⟨a,ha,heq⟩ := hmem
  have hderived : Nat.card (commutator a.fixedSubgroup) = 3840 := by
    have hc := derived_card_congr (MulAut.fixedSubgroupCongr e a)
    change Nat.card (commutator a.fixedSubgroup) =
      Nat.card (commutator (MulAut.congr e a).fixedSubgroup) at hc
    change MulAut.congr e a = MulAut.conj x at heq
    rw [heq] at hc
    exact hc.trans (central_class_derived_card x hx)
  refine ⟨hcard,a,ha,?_,hderived⟩
  intro hone
  have hx1 : x = 1 := HSInner.conj_injective (by simpa only [hone,map_one] using heq.symm)
  rw [hx1,isConj_one_left] at hx
  exact EvenLocalCandidates.CentralInvolutionCore.e0_nontrivial hx
end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.Sporadic.HSGeometry
