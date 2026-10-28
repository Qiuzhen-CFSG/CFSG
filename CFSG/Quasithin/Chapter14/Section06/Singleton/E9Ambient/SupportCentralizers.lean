module
public import CFSG.Quasithin.Chapter14.Section06.Singleton.E9Ambient.PointNormalizers

/-!
# Exact support centralizers at both elementary-nine endpoints

Each of the two order-eight cubic supports meets the literal index-two
critical core denominator in a four-group. These intersections centralize
the opposite span. Their join has order eight and fills its centralizer:
a larger join would fill the denominator, contradicting its nontrivial
point commutator. The order-thirty-two bound is obtained from the actual
M-plane placement in PointNormalizers, not a local model calculation.

Reversal transports the same formula through the critical conjugator,
retaining the other original core intersection. These statements describe
both centralizers; they do not supply the remaining ambient contradiction.
Source: Aschbacher--Smith, 14.6.12, printed p.1031, and F.9.13--17,
pp.322--324 of refs/quasithin.pdf, using the original support lifts and
point commutators in SourceSingletonCompatibility.NineAmbientParallel.
-/

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

private theorem support_centralizer {G : Type*} [Group G] [Finite G]
    (U D B Z : Subgroup G) (W : Fin 2 → Subgroup G) [IsMulCommutative U]
    (hDU : D ≤ U) (hDi : D.relIndex U = 2) (hUc : Nat.card U = 32)
    (hW : ∀ k, W k ≤ U) (hWc : ∀ k, Nat.card (W k) = 8)
    (hWI : W 0 ⊓ W 1 = Z) (hZc : Nat.card Z = 2) (hZD : Z ≤ D)
    (hc : ∀ k, D ⊓ W k ≤ centralizer (B : Set G))
    (hn : ¬ D ≤ centralizer (B : Set G))
    (hCD : U ⊓ centralizer (B : Set G) ≤ D) :
    (∀ k, Nat.card (D ⊓ W k : Subgroup G) = 4) ∧
    U ⊓ centralizer (B : Set G) = (D ⊓ W 0) ⊔ (D ⊓ W 1) ∧
    Nat.card (U ⊓ centralizer (B : Set G) : Subgroup G) = 8 ∧
    (U ⊓ centralizer (B : Set G)).relIndex D = 2 := by
  let C := U ⊓ centralizer (B : Set G)
  let L := (D ⊓ W 0) ⊔ (D ⊓ W 1)
  have hLC : L ≤ C := sup_le (le_inf (inf_le_left.trans hDU) (hc 0))
    (le_inf (inf_le_left.trans hDU) (hc 1))
  have hDc : Nat.card D = 16 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup G) D U bot_le hDU
    rw [relIndex_bot_left,relIndex_bot_left,hDi,hUc] at hh
    omega
  have hCn : C ≠ D := by
    intro he
    exact hn (he ▸ (inf_le_right : C ≤ centralizer (B : Set G)))
  have hCI : 2 ≤ C.relIndex D := by
    have hp : C.relIndex D ≠ 0 := index_ne_zero_of_finite
    have hn1 : C.relIndex D ≠ 1 := fun he => hCn (le_antisymm hCD (relIndex_eq_one.mp he))
    omega
  have hCc : Nat.card C ≤ 8 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup G) C D bot_le hCD
    rw [relIndex_bot_left,relIndex_bot_left,hDc] at hh
    nlinarith
  have hLc : Nat.card L ≤ 8 := (card_le_of_le hLC).trans hCc
  have hWi (k : Fin 2) : (D ⊓ W k).relIndex (W k) ≤ 2 := by
    rw [inf_relIndex_right]
    exact hDi ▸ relIndex_le_of_le_right (hW k) (by rw [hDi]; decide)
  have hWcards (k : Fin 2) : Nat.card (D ⊓ W k : Subgroup G) = 4 ∨
      Nat.card (D ⊓ W k : Subgroup G) = 8 := by
    have hp : (D ⊓ W k).relIndex (W k) ≠ 0 := index_ne_zero_of_finite
    have hh := relIndex_mul_relIndex (⊥ : Subgroup G) (D ⊓ W k) (W k) bot_le inf_le_right
    rw [relIndex_bot_left,relIndex_bot_left,hWc k] at hh
    have hidx := hWi k
    have hi : (D ⊓ W k).relIndex (W k) = 1 ∨ (D ⊓ W k).relIndex (W k) = 2 := by omega
    rcases hi with hi | hi <;> rw [hi] at hh <;> omega
  have hI : (D ⊓ W 0) ⊓ (D ⊓ W 1) = Z := by
    apply le_antisymm
    · exact (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)).trans hWI.le
    · exact le_inf (le_inf hZD (hWI.ge.trans inf_le_left))
        (le_inf hZD (hWI.ge.trans inf_le_right))
  have hN : D ⊓ W 1 ≤ normalizer ((D ⊓ W 0 : Subgroup G) : Set G) :=
    ((inf_le_right.trans (hW 1)).trans
      ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
        (centralizer_le ((inf_le_right : D ⊓ W 0 ≤ W 0).trans (hW 0))))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes (D ⊓ W 0) (D ⊓ W 1) hN
  rw [hI,hZc] at hprod
  change Nat.card (D ⊓ W 0 : Subgroup G) * Nat.card (D ⊓ W 1 : Subgroup G) = 2 * Nat.card L at hprod
  have hfour : ∀ k, Nat.card (D ⊓ W k : Subgroup G) = 4 := by
    have h0 := hWcards 0
    have h1 := hWcards 1
    have hx : Nat.card (D ⊓ W 0 : Subgroup G) = 4 ∧
        Nat.card (D ⊓ W 1 : Subgroup G) = 4 := by
      rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
      · exact ⟨h0,h1⟩
      all_goals rw [h0,h1] at hprod; omega
    intro k
    fin_cases k
    · exact hx.1
    · exact hx.2
  have hLeight : Nat.card L = 8 := by rw [hfour 0,hfour 1] at hprod; omega
  have he : C = L := (eq_of_le_of_card_ge hLC (by rw [hLeight]; exact hCc)).symm
  refine ⟨hfour,he,by change Nat.card C = 8; rw [he,hLeight],?_⟩
  have hh := relIndex_mul_relIndex (⊥ : Subgroup G) C D bot_le hCD
  rw [relIndex_bot_left,relIndex_bot_left,hDc,he,hLeight] at hh
  change C.relIndex D = 2
  rw [he]
  omega

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
include hG hempty hM hu hmany hcard e hab
open OddCriticalPair.OrthogonalSource

/-- The actual core denominator meets each cubic support in a four-group.
These two four-groups generate exactly the centralizer of the opposite span,
which has order eight and index two in the denominator. This holds at every
critical endpoint, hence also at every reverse endpoint. -/
theorem source_singleton_nine_support_centralizer
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation) (hd : d.FittingFull)
    (hone : Nat.card d.Index = 1)
    (hnine : Nat.card (pResidual 2 (J ⧸ pCore 2 J)) = 9)
    (s : ChapterD.FittingConfigurations.SupportFactors (movedRepresentation a)
      (pResidual 2 (J ⧸ pCore 2 J)) 2) :
    let D : ChapterF.Section09.Setup G :=
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
    let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1
    ∀ i : h.CriticalEndpoint,
      let A := fun k => (s.ambient k).comap (QuotientGroup.mk' (pCore 2 J))
      let W := fun k => ⁅D.UH,((pResidual 2 (A k)).map (A k).subtype).map J.subtype⁆
      let E := D.UH ⊓ i.conjugate D.QH
      let C := D.UH ⊓ centralizer (i.conjugate D.UH : Set G)
      (∀ k, Nat.card (E ⊓ W k : Subgroup G) = 4) ∧
      C = (E ⊓ W 0) ⊔ (E ⊓ W 1) ∧
      Nat.card C = 8 ∧ C.relIndex E = 2 := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
  let : IsElementaryAbelian 2 D.UH :=
    ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)›
  let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1
  change ∀ i : h.CriticalEndpoint, _
  intro i
  let A := fun k => (s.ambient k).comap (QuotientGroup.mk' (pCore 2 J))
  let W := fun k => ⁅D.UH,((pResidual 2 (A k)).map (A k).subtype).map J.subtype⁆
  let E := D.UH ⊓ i.conjugate D.QH
  let C := D.UH ⊓ centralizer (i.conjugate D.UH : Set G)
  obtain ⟨hden,_,hindex,_⟩ := source_singleton_nine_reciprocal_core_indices
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine i
  have hCD : C ≤ E := by
    have hc : ⁅C,i.conjugate D.UH⁆ = ⊥ :=
      commutator_eq_bot_iff_le_centralizer.mpr inf_le_right
    exact (le_commutatorPreimage (show C ≤ D.UH from inf_le_left)
      (hc.le.trans bot_le)).trans hden.le
  have hb := (source_rankTwo_critical_track_bounds
    hG T hempty hM hu hmany hcard e hab J hJ.1).1
  have hZC : D.V₁ ≤ C := le_inf (h.point_lt.le.trans (le_conjugateSpanBy _ _))
    ((le_centralizer_iff.mp h.H_centralizes).trans (centralizer_le (i.large_le hb)))
  have hn : ¬ E ≤ centralizer (i.conjugate D.UH : Set G) := by
    intro hc
    have he := commutator_eq_bot_iff_le_centralizer.mpr hc
    rw [source_singleton_nine_core_commutator_point
      hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine i] at he
    have hp : Nat.card (i.conjugate D.V₁) = 2 :=
      (card_map_of_injective (MulAut.conj i.representative).injective).trans h.point_card
    rw [he,card_bot] at hp
    omega
  obtain ⟨_,hWc,hWI,_,_⟩ := source_singleton_nine_lifted_supports
    hG T hempty hM hu hmany hcard e hab J hJ hs a s
  exact support_centralizer D.UH E (i.conjugate D.UH) D.V₁ W inf_le_left hindex
    (source_singleton_nine_whole_span_moved
      hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine i).2
    (fun k => le_normalizer_iff_commutator_le_left.mp
      ((map_subtype_le _).trans a.normalizes))
    hWc hWI h.point_card (hZC.trans hCD)
    (fun k => commutator_eq_bot_iff_le_centralizer.mp
      (source_singleton_nine_denominator_support_centralizes
        hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine s i k))
    hn hCD


/-- The opposite centralizer is the inverse transport of the support formula
at a genuine reverse endpoint. Its denominator is the other original core
intersection, not a chosen isomorphic copy. -/
theorem source_singleton_nine_reverse_support_centralizer
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation) (hd : d.FittingFull)
    (hone : Nat.card d.Index = 1)
    (hnine : Nat.card (pResidual 2 (J ⧸ pCore 2 J)) = 9)
    (s : ChapterD.FittingConfigurations.SupportFactors (movedRepresentation a)
      (pResidual 2 (J ⧸ pCore 2 J)) 2) :
    let D : ChapterF.Section09.Setup G :=
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
    let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1
    ∀ i : h.CriticalEndpoint,
      let A := fun k => (s.ambient k).comap (QuotientGroup.mk' (pCore 2 J))
      let W := fun k => ⁅D.UH,((pResidual 2 (A k)).map (A k).subtype).map J.subtype⁆
      let C := i.conjugate D.UH ⊓ centralizer (D.UH : Set G)
      ∃ j : h.CriticalEndpoint,
        (∀ B : Subgroup G, J ≤ normalizer (B : Set G) →
          (i.conjugate B).map (MulAut.conj j.representative).toMonoidHom = B) ∧
        C = (((D.UH ⊓ j.conjugate D.QH) ⊓ W 0) ⊔
          ((D.UH ⊓ j.conjugate D.QH) ⊓ W 1)).conjBy j.representative⁻¹ ∧
        Nat.card C = 8 ∧ C.relIndex (i.conjugate D.UH ⊓ D.QH) = 2 := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
  let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1
  change ∀ i : h.CriticalEndpoint, _
  intro i
  let A := fun k => (s.ambient k).comap (QuotientGroup.mk' (pCore 2 J))
  let W := fun k => ⁅D.UH,((pResidual 2 (A k)).map (A k).subtype).map J.subtype⁆
  let C := i.conjugate D.UH ⊓ centralizer (D.UH : Set G)
  obtain ⟨hq,hb,_,_⟩ := source_singleton_nine_critical_reciprocity
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine
  obtain ⟨j,hj⟩ := i.reverse_labels hb
    (source_rankTwo_critical_core_escape_of_ratio_two
      hG T hempty hM hu hmany hcard e hab J hJ.1 a hq i)
  have hUN : J ≤ normalizer (D.UH : Set G) := le_normalizer_conjugateSpanBy _ _
  let Cj := D.UH ⊓ centralizer (j.conjugate D.UH : Set G)
  let Ej := D.UH ⊓ j.conjugate D.QH
  have hC : C.map (MulAut.conj j.representative).toMonoidHom = Cj := by
    change (i.conjugate D.UH ⊓ centralizer (D.UH : Set G)).map _ = Cj
    rw [map_inf _ _ _ (MulAut.conj j.representative).injective,
      map_centralizer_equiv,hj D.UH hUN]
    rfl
  have hE : (i.conjugate D.UH ⊓ D.QH).map
      (MulAut.conj j.representative).toMonoidHom = Ej := by
    rw [map_inf _ _ _ (MulAut.conj j.representative).injective,hj D.UH hUN]
  obtain ⟨_,hjoin,hcardj,hindex⟩ := source_singleton_nine_support_centralizer
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine s j
  change Cj = (Ej ⊓ W 0) ⊔ (Ej ⊓ W 1) at hjoin
  refine ⟨j,hj,?_,?_,?_⟩
  · have hh := congrArg (fun B : Subgroup G => B.conjBy j.representative⁻¹)
      (hC.trans hjoin)
    change (C.conjBy j.representative).conjBy j.representative⁻¹ = _ at hh
    rwa [conjBy_inv] at hh
  · have he := card_map_of_injective (K := C)
      (f := (MulAut.conj j.representative).toMonoidHom) (MulAut.conj j.representative).injective
    rw [hC] at he
    exact he.symm.trans hcardj
  · have he := relIndex_map_map_of_injective
      (f := (MulAut.conj j.representative).toMonoidHom)
      C (i.conjugate D.UH ⊓ D.QH) (MulAut.conj j.representative).injective
    rw [hC,hE] at he
    exact he.symm.trans hindex

end CFSG.Quasithin.Chapter14.Section06
