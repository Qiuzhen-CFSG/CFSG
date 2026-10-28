module
public import CFSG.Quasithin.Chapter14.Section06.SourceIntersection
public import Theory.GroupTheory.CentralCommutatorQuotient
public import Theory.GroupTheory.RelativeCentralLayerCentralizerIndex
public import Theory.GroupTheory.GeneralizedFitting.SemisimpleCenter
public import Theory.GroupTheory.Fitting.Core
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.ElementaryAbelian.BinaryQuotientRank

/-!
# The quotient-rank comparison in original 14.6.8

The odd core of I is trivial by 14.6.7. If F*(I) differs from O₂(I), an
ordinary component therefore exists. It centralizes O₂(I), whereas the
original marked involution does not centralize that component. Thus the
central line Z meets O₂(I) trivially.

Put P = C_QH(u). The intersection UH ∩ O₂(I) centralizes P and is a proper
subgroup of C_UH(P), since the latter contains Z. The central commutator map
on QH has image of order at most two. The existing relative centralizer-index
bound then gives |C_UH(P):C_UH(QH)| ≤ 2, yielding the required comparison of
quotient orders. Finally the literal image of UH in I/O₂(I) is elementary
abelian, so its binary rank bounds the two-rank of that quotient below.

The displayed logarithmic ranks are exactly the dimensions of the respective
elementary abelian quotients by `Subgroup.log_relIndex_eq_quotient_finrank`.
Only u ∈ UH and the original overgroup and Sylow data are needed here.
Source: Aschbacher–Smith, refs/quasithin.pdf, 14.6.8, printed pp.1024–1025.
-/

public section

open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem card_mul_relative (A B : Subgroup G) (h : A ≤ B) :
    Nat.card A * A.relIndex B = Nat.card B := by
  simpa only [relIndex_bot_left] using
    relIndex_mul_relIndex (⊥ : Subgroup G) A B bot_le h

private theorem central_binary_disjoint_index
    (U Q Z N : Subgroup G) (u : G) (hu : u ∈ U)
    (hZU : Z ≤ U) (hZQ : Z ≤ centralizer (Q : Set G))
    (hUZ : U ≤ centralizer (Z : Set G)) (hZcard : Nat.card Z = 2)
    (hcomm : ⁅U,Q⁆ ≤ Z) (hZN : Z ⊓ N = ⊥) (hZnotN : ¬ Z ≤ N)
    (hPN : Q ⊓ centralizer ({u} : Set G) ≤ normalizer (N : Set G)) :
    (centralizer (Q : Set G)).relIndex U ≤ N.relIndex U := by
  classical
  let P := Q ⊓ centralizer ({u} : Set G)
  let A := U ⊓ centralizer (P : Set G)
  let C := U ⊓ centralizer (Q : Set G)
  let W := U ⊓ N
  have hWA : W ≤ A := by
    refine le_inf inf_le_left (commutator_eq_bot_iff_le_centralizer.mp ?_)
    apply eq_bot_iff.mpr
    rw [←hZN]
    refine le_inf ((commutator_mono inf_le_left inf_le_left).trans hcomm) ?_
    exact (commutator_mono inf_le_right le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp hPN)
  have hZA : Z ≤ A := le_inf hZU (hZQ.trans (centralizer_le inf_le_left))
  have hCA : C ≤ A := inf_le_inf_left _ (centralizer_le inf_le_left)
  have hcount : Nat.card W ≤ Nat.card C := by
    by_cases hup : u ∈ centralizer (Q : Set G)
    · have hPQ : P = Q := inf_eq_left.mpr (by
        intro q hq
        exact mem_centralizer_singleton_iff.mpr (hup q hq))
      have hWC : W ≤ C := by simpa only [A,hPQ] using hWA
      exact Nat.card_le_card_of_injective (inclusion hWC) (inclusion_injective hWC)
    · have hvalue (x : G) (hx : x ∈ Q) : ⁅u,x⁆ ∈ Z :=
        hcomm (commutator_mem_commutator hu hx)
      let f := centralCommutatorHom Q Z hZQ u hvalue
      have hker : f.ker = (centralizer ({u} : Set G)).subgroupOf Q :=
        centralCommutatorHom_ker Q Z hZQ u hvalue
      have hrange : f.range = ⊤ := by
        let : Fact (Nat.card Z).Prime := ⟨hZcard ▸ Nat.prime_two⟩
        apply f.range.eq_bot_or_eq_top_of_prime_card.resolve_left
        intro hb
        apply hup
        intro q hq
        have hv : f ⟨q,hq⟩ = 1 := by
          exact mem_bot.mp (hb ▸ show f ⟨q,hq⟩ ∈ f.range from ⟨⟨q,hq⟩,rfl⟩)
        exact (commutatorElement_eq_one_iff_mul_comm.mp (congrArg Subtype.val hv)).symm
      have hPindex : (P.subgroupOf Q).index = 2 := by
        have he : P.subgroupOf Q = f.ker := by
          rw [hker]
          ext x
          exact and_iff_right x.property
        rw [he,index_ker,hrange,card_top,hZcard]
      have hbound := relIndex_centralizer_le_card_of_central_index_two_layer
        A Q P Z inf_le_right (inf_le_left.trans hUZ) hPindex
        ((commutator_mono inf_le_left le_rfl).trans hcomm)
      have hcentral : (centralizer (Q : Set G)).relIndex A = C.relIndex A := by
        apply congrArg (fun K : Subgroup A => K.index)
        ext x
        exact (and_iff_right x.property.1).symm
      rw [hcentral,hZcard] at hbound
      have hstrict : ¬ A ≤ W := by
        intro hh
        exact hZnotN (hZA.trans (hh.trans inf_le_right))
      have htwo : 2 ≤ W.relIndex A := by
        have hh := one_lt_index_of_ne_top (H := W.subgroupOf A)
          (fun he => hstrict (subgroupOf_eq_top.mp he))
        exact hh
      have hw := card_mul_relative W A hWA
      have hc := card_mul_relative C A hCA
      have hwlower := Nat.mul_le_mul_left (Nat.card W) htwo
      have hcupper := Nat.mul_le_mul_left (Nat.card C) hbound
      nlinarith
  have hw := card_mul_relative W U inf_le_left
  have hc := card_mul_relative C U inf_le_left
  have hpos := Nat.card_pos (α := C)
  have hrel : C.relIndex U ≤ W.relIndex U := by
    apply Nat.le_of_mul_le_mul_left (show Nat.card C * C.relIndex U ≤
        Nat.card C * W.relIndex U from ?_) hpos
    calc
      Nat.card C * C.relIndex U = Nat.card U := hc
      _ = Nat.card W * W.relIndex U := hw.symm
      _ ≤ Nat.card C * W.relIndex U := Nat.mul_le_mul_right _ hcount
  simpa only [W,C,inf_relIndex_left] using hrel

private theorem elementary_quotient_rank_bound
    (I U : Subgroup G) (hUI : U ≤ I) [IsElementaryAbelian 2 U] :
    Nat.log 2 ((I.pCoreIn 2).relIndex U) ≤ primeRank 2 (I ⧸ pCore 2 I) := by
  let A := U.subgroupOf I
  let q := QuotientGroup.mk' (pCore 2 I)
  let E := A.map q
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf hUI
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map q
  have hcore : (I.pCoreIn 2).subgroupOf I = pCore 2 I := by
    exact comap_map_eq_self_of_injective I.subtype_injective _
  have hcard : Nat.card E = (I.pCoreIn 2).relIndex U := by
    rw [←relIndex_subgroupOf hUI,hcore]
    simpa only [A,E,q,QuotientGroup.ker_mk'] using
      (relIndex_ker A q).symm
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
  rw [←hcard,hn,Nat.log_pow (by decide)]
  exact IsElementaryAbelian.primeRank_ge_of_card E hn

open Chapter12.Section08 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

/-- Original 14.6.8 on the literal two-core and centralizer quotient indices. -/
theorem source_lemma_14_6_8
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (I : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (S : Sylow 2 I) (hS : (S : Subgroup I).map I.subtype = (T : Subgroup G) ⊓ I)
    (hF : generalizedFitting I ≠ pCore 2 I) :
    Nat.log 2 ((I.pCoreIn 2).relIndex (conjugateSpanBy (localModule T M) H)) ≤
        primeRank 2 (I ⧸ pCore 2 I) ∧
      Nat.log 2 ((centralizer (H.pCoreIn 2 : Set G)).relIndex
        (conjugateSpanBy (localModule T M) H)) ≤
      Nat.log 2 ((I.pCoreIn 2).relIndex (conjugateSpanBy (localModule T M) H)) := by
  classical
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
  have h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
  let : IsElementaryAbelian 2 D.UH := h.UH_elementary_of_V_le_QH
    ((le_conjugateSpanBy D.V D.H).trans h.UH_le_QH)
  have hUI : D.UH ≤ I := by
    intro v hv
    apply hI.1.2.1
    refine ⟨h.UH_le_QH.trans h.QH_le_T hv,?_⟩
    exact mem_centralizer_singleton_iff.mpr
      (congrArg D.UH.subtype (mul_comm (⟨v,hv⟩ : D.UH) ⟨u,hu⟩))
  have hZU : D.V₁ ≤ D.UH := h.point_lt.le.trans (le_conjugateSpanBy _ _)
  have hZQ : D.V₁ ≤ centralizer (D.QH : Set G) :=
    le_centralizer_iff.mp ((pCoreIn_le 2 H).trans h.H_centralizes)
  obtain ⟨⟨z,hz,h115⟩,_,hodd⟩ :=
    source_lemma_14_6_7_initial hG T hempty hM hunique hmany hcard e hab H hH
      u hu I hI.1 S hS
  have hcomp : ∃ K : Subgroup I, IsComponent I K := by
    by_contra hnone
    have hE : componentLayer I = ⊥ := by
      apply le_bot_iff.mp
      exact sSup_le fun K hK => (hnone ⟨K,hK⟩).elim
    apply hF
    rw [generalizedFitting,hE,sup_bot_eq,Fitting_eq_pcore I 2 hodd]
  obtain ⟨K,hK⟩ := hcomp
  have hZnotN : ¬ D.V₁ ≤ I.pCoreIn 2 := by
    intro hZN
    have hzI : z ∈ I := hUI (hZU hz)
    have hzi : (⟨z,hzI⟩ : I) ∈ pCore 2 I := by
      obtain ⟨a,ha,he⟩ := hZN hz
      have haeq : a = (⟨z,hzI⟩ : I) := Subtype.ext he
      exact haeq ▸ ha
    let : Group.IsNilpotent (pCore 2 I) := pCore_isNilpotent
    have hcentral := hK.le_centralizer_of_solvable_normal (pCore 2 I)
    apply (h115.component_inputs K hK).1
    intro k hk
    obtain ⟨a,ha,rfl⟩ := hk
    apply h115.centralizer_le
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact congrArg I.subtype (hcentral ha ⟨z,hzI⟩ hzi)
  have hZN : D.V₁ ⊓ I.pCoreIn 2 = ⊥ := by
    let : Fact (Nat.card D.V₁).Prime := ⟨h.point_card ▸ Nat.prime_two⟩
    rcases ((I.pCoreIn 2).subgroupOf D.V₁).eq_bot_or_eq_top_of_prime_card with hb | ht
    · apply eq_bot_iff.mpr
      intro a ha
      exact congrArg D.V₁.subtype
        (mem_bot.mp (hb ▸ show (⟨a,ha.1⟩ : D.V₁) ∈ (I.pCoreIn 2).subgroupOf D.V₁ from ha.2))
    · exact (hZnotN (subgroupOf_eq_top.mp ht)).elim
  have hPN : D.QH ⊓ centralizer ({u} : Set G) ≤ normalizer (I.pCoreIn 2 : Set G) :=
    ((inf_le_inf_right _ h.QH_le_T).trans hI.1.2.1).trans
      (I.le_normalizer.trans (normalizer_le_normalizer_characteristic_image I (pCore 2 I)))
  exact ⟨elementary_quotient_rank_bound I D.UH hUI,
    Nat.log_mono_right (central_binary_disjoint_index D.UH D.QH D.V₁ (I.pCoreIn 2)
      u hu hZU hZQ (h.UH_le_H.trans h.H_centralizes) h.point_card
      h.commutator_UH_QH_le_point hZN hZnotN hPN)⟩

end CFSG.Quasithin.Chapter14.Section06
