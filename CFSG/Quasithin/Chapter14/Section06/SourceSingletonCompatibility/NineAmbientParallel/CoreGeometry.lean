module
public import CFSG.Quasithin.Chapter14.Section06.SourceSingletonCompatibility.NineQuotient
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.SelectedEndpoint
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.ModuleBound.OriginalF916
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.EndpointKernels

/-!
# Both core denominators and point lines in the elementary-nine branch

The original action kernel identifies each critical commutator denominator
with the corresponding intersection with O₂(J). F.9.17 transports the
index-two image through one reverse endpoint, giving index two at both
ends of the same pair. Cubic ratio two forces the denominator commutator
to fill the opposite point line at every critical endpoint. Reversing
again recovers the original point line. These two distinct lines generate
a four-group in the mutual commutator, while the two core denominators
centralize one another.

All statements use the original J, Sylow subgroup, residual and quotient
maps. The argument uses neither the exchanged factors of 14.6.12 nor the
alternatives of 14.6.13. It supplies paired geometry for the still open
ambient-nine exclusion; it does not establish that exclusion.

Source: Aschbacher--Smith, 14.6.12, printed p.1031, and F.9.2(3),
F.9.13--17, printed pp.318,322--324 of refs/quasithin.pdf.
-/

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



open Chapter13.Section08.SourceCompletion
open Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences
open Chapter15.Section03.AbelianAmalgam.GenerationOne

omit hG T hempty hM hu hmany hcard e hab in
private theorem critical_denominators
    {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
    (hUV : D.UH = D.VH) (i : h.CriticalEndpoint) (hb : 3 ≤ h.b) :
    commutatorPreimage D.UH (i.conjugate D.UH) (i.conjugate D.V₁) =
      D.UH ⊓ i.conjugate D.QH ∧
    commutatorPreimage (i.conjugate D.UH) D.UH D.V₁ =
      i.conjugate D.UH ⊓ D.QH := by
  have hback : D.UH.conjBy i.representative⁻¹ ≤ D.H := by
    have hh := map_mono (f := (MulAut.conj i.representative⁻¹).toMonoidHom)
      (hUV ▸ i.reverse_le hb)
    change D.UH.conjBy i.representative⁻¹ ≤
      (D.H.conjBy i.representative).conjBy i.representative⁻¹ at hh
    rwa [conjBy_inv] at hh
  constructor
  · have he := congrArg (fun A : Subgroup G => A.map
        (MulAut.conj i.representative).toMonoidHom)
      (f9_commutatorPreimage_eq D h (D.UH.conjBy i.representative⁻¹) hback)
    rw [map_commutatorPreimage_equiv _ _ _ _
      (hback.trans (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))),
      map_inf _ _ _ (MulAut.conj i.representative).injective] at he
    change commutatorPreimage ((D.UH.conjBy i.representative⁻¹).conjBy i.representative)
      (i.conjugate D.UH) (i.conjugate D.V₁) =
      (D.UH.conjBy i.representative⁻¹).conjBy i.representative ⊓ i.conjugate D.QH at he
    rwa [conjBy_inv'] at he
  · exact f9_commutatorPreimage_eq D h _ (hUV ▸ i.large_le hb)

/-- Both original critical denominators have index two. -/
theorem source_singleton_nine_reciprocal_core_indices
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation) (hd : d.FittingFull)
    (hone : Nat.card d.Index = 1)
    (hnine : Nat.card (pResidual 2 (J ⧸ pCore 2 J)) = 9) :
    let D : ChapterF.Section09.Setup G :=
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
    let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1
    ∀ i : h.CriticalEndpoint,
      commutatorPreimage D.UH (i.conjugate D.UH) (i.conjugate D.V₁) =
        D.UH ⊓ i.conjugate D.QH ∧
      commutatorPreimage (i.conjugate D.UH) D.UH D.V₁ =
        i.conjugate D.UH ⊓ D.QH ∧
      (D.UH ⊓ i.conjugate D.QH).relIndex D.UH = 2 ∧
      (i.conjugate D.UH ⊓ D.QH).relIndex (i.conjugate D.UH) = 2 := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
  let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1
  obtain ⟨hq,hb,_,_⟩ := source_singleton_nine_critical_reciprocity
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine
  have hQN : J ≤ normalizer (D.QH : Set G) := by
    have hh := (pCore 2 J).le_normalizer_map J.subtype
    simpa only [ChapterF.Section09.Setup.QH,pCoreIn,normalizer_eq_top,
      ←MonoidHom.range_eq_map,range_subtype] using hh
  change ∀ i : h.CriticalEndpoint, _
  intro i
  obtain ⟨j,hj⟩ := i.reverse_labels hb
    (source_rankTwo_critical_core_escape_of_ratio_two
      hG T hempty hM hu hmany hcard e hab J hJ.1 a hq i)
  have hm := relIndex_map_map_of_injective (f := (MulAut.conj j.representative).toMonoidHom)
    (D.UH ⊓ i.conjugate D.QH) D.UH
    (MulAut.conj j.representative).injective
  rw [map_inf _ _ _ (MulAut.conj j.representative).injective,hj D.QH hQN] at hm
  have hi := (source_singleton_nine_critical_image
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine i).2
  have hjidx := (source_singleton_nine_critical_image
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine j).2
  exact ⟨(critical_denominators h rfl i hb).1,
    (critical_denominators h rfl i hb).2,hm.symm.trans hjidx,hi⟩

/-- Every original nine endpoint recovers its opposite point from the literal
core intersection; the choice is not restricted to a selected endpoint. -/
theorem source_singleton_nine_core_commutator_point
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation) (hd : d.FittingFull)
    (hone : Nat.card d.Index = 1)
    (hnine : Nat.card (pResidual 2 (J ⧸ pCore 2 J)) = 9) :
    let D : ChapterF.Section09.Setup G :=
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
    let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1
    ∀ i : h.CriticalEndpoint,
      ⁅D.UH ⊓ i.conjugate D.QH,i.conjugate D.UH⁆ = i.conjugate D.V₁ := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
  let : IsElementaryAbelian 2 D.UH :=
    ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)›
  let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1
  obtain ⟨hq,hb,_,_⟩ := source_singleton_nine_critical_reciprocity
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine
  change ∀ i : h.CriticalEndpoint, _
  intro i
  have hc : Nat.card (actorImage J (i.conjugate D.UH)) = 2 :=
    (source_singleton_nine_critical_image
      hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine i).1
  obtain ⟨b,hb2⟩ := exists_prime_orderOf_dvd_card'
    (G := actorImage J (i.conjugate D.UH)) 2 (by rw [hc])
  have hbo : orderOf (b : J ⧸ pCore 2 J) = 2 := (Subgroup.orderOf_coe b).trans hb2
  have hz : zpowers (b : J ⧸ pCore 2 J) = actorImage J (i.conjugate D.UH) := by
    apply eq_of_le_of_card_ge (zpowers_le.mpr b.property)
    rw [Nat.card_zpowers,hbo,hc]
  obtain ⟨he,hr,hquad,_⟩ := involution_actor_rank_and_fixedCodim a.representation b hbo
  rw [hz] at he hr hquad
  have hl : cubicRatio a.representation ≤ actionRatio a.representation
      (actorImage J (i.conjugate D.UH)) :=
    iInf_le_of_le _ (iInf_le_of_le ⟨he,isCubic_of_isQuadratic hquad⟩ le_rfl)
  have hlow : 2 ≤ fixedCodim a.representation (actorImage J (i.conjugate D.UH)) := by
    have hh : (2 : ENNReal) ≤ (fixedCodim a.representation
        (actorImage J (i.conjugate D.UH)) : ENNReal) := by
      simpa only [hq,actionRatio,hr,Nat.cast_one,div_one] using hl
    exact_mod_cast hh
  obtain ⟨hden,_,hindex,_⟩ := source_singleton_nine_reciprocal_core_indices
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine i
  have hnorm : D.UH ≤ normalizer (i.conjugate D.V₁ : Set G) := by
    have hn := map_mono (f := (MulAut.conj i.representative).toMonoidHom)
      (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
    rw [map_equiv_normalizer_eq] at hn
    exact (i.reverse_le hb).trans hn
  have hpoint : Nat.card (i.conjugate D.V₁) = 2 :=
    (card_map_of_injective (MulAut.conj i.representative).injective).trans h.point_card
  have hstrict : Nat.log 2 ((commutatorPreimage D.UH (i.conjugate D.UH)
      (i.conjugate D.V₁)).relIndex D.UH) <
      fixedCodim a.representation (actorImage J (i.conjugate D.UH)) := by
    rw [hden,hindex]
    norm_num
    omega
  have hh := f9_denominator_commutator_eq_point
    (ModuleBound.OriginalF916.conjugationSection a h.H_centralizes)
    (i.large_le hb) hnorm hpoint hstrict
  change ⁅commutatorPreimage D.UH (i.conjugate D.UH) (i.conjugate D.V₁),
    i.conjugate D.UH⁆ = i.conjugate D.V₁ at hh
  rwa [hden] at hh


/-- The same critical pair has both point commutators and a four-group of
point lines in its mutual commutator. The actual original cores are retained. -/
theorem source_singleton_nine_paired_point_lines
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation) (hd : d.FittingFull)
    (hone : Nat.card d.Index = 1)
    (hnine : Nat.card (pResidual 2 (J ⧸ pCore 2 J)) = 9) :
    let D : ChapterF.Section09.Setup G :=
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
    let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1
    ∀ i : h.CriticalEndpoint,
      ⁅D.UH ⊓ i.conjugate D.QH,i.conjugate D.UH⁆ = i.conjugate D.V₁ ∧
      ⁅i.conjugate D.UH ⊓ D.QH,D.UH⁆ = D.V₁ ∧
      D.V₁ ⊔ i.conjugate D.V₁ ≤ ⁅D.UH,i.conjugate D.UH⁆ ∧
      D.V₁ ⊓ i.conjugate D.V₁ = ⊥ ∧
      Nat.card (D.V₁ ⊔ i.conjugate D.V₁ : Subgroup G) = 4 ∧
      ⁅D.UH ⊓ i.conjugate D.QH,i.conjugate D.UH ⊓ D.QH⁆ = ⊥ := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
  let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1
  obtain ⟨hq,hb,_,_⟩ := source_singleton_nine_critical_reciprocity
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine
  have hUN : J ≤ normalizer (D.UH : Set G) := le_normalizer_conjugateSpanBy _ _
  change ∀ i : h.CriticalEndpoint, _
  intro i
  obtain ⟨j,hj⟩ := i.reverse_labels hb
    (source_rankTwo_critical_core_escape_of_ratio_two
      hG T hempty hM hu hmany hcard e hab J hJ.1 a hq i)
  have hi := source_singleton_nine_core_commutator_point
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine i
  have hreverse : ⁅i.conjugate D.UH ⊓ D.QH,D.UH⁆ = D.V₁ := by
    apply map_injective (f := (MulAut.conj j.representative).toMonoidHom)
      (MulAut.conj j.representative).injective
    rw [map_commutator,map_inf _ _ _ (MulAut.conj j.representative).injective,
      hj D.UH hUN]
    exact source_singleton_nine_core_commutator_point
      hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine j
  have hjoin : D.V₁ ⊔ i.conjugate D.V₁ ≤ ⁅D.UH,i.conjugate D.UH⁆ := by
    apply sup_le
    · rw [←hreverse,commutator_comm D.UH]
      exact commutator_mono inf_le_left le_rfl
    · rw [←hi]
      exact commutator_mono inf_le_left le_rfl
  have hpc : Nat.card (i.conjugate D.V₁) = 2 :=
    (card_map_of_injective (MulAut.conj i.representative).injective).trans h.point_card
  have hne : D.V₁ ≠ i.conjugate D.V₁ := by
    intro he
    apply source_rankTwo_critical_not_mem_Mc hG T hempty hM hu hmany hcard e hab J hJ.1 i
    have hMc : Mc = centralizer (centralInvolutions T : Set G) :=
      (source_lemma_14_1_18 hG T hempty hM hu hmany hcard e).2.2.2.2.2.2.2.2.2.2.2.2.2.1
    apply hMc.ge
    exact normalizer_le_centralizer_of_card_two D.V₁ h.point_card
      (mem_normalizer_iff_map_conj_eq.mpr he.symm)
  have hinf : D.V₁ ⊓ i.conjugate D.V₁ = ⊥ :=
    inf_eq_bot_of_card_two_of_ne _ _ h.point_card hpc hne
  have hcomm : ⁅D.UH ⊓ i.conjugate D.QH,i.conjugate D.UH ⊓ D.QH⁆ = ⊥ := by
    apply bot_unique
    rw [←hinf]
    apply le_inf
    · calc
        ⁅D.UH ⊓ i.conjugate D.QH,i.conjugate D.UH ⊓ D.QH⁆ =
            ⁅i.conjugate D.UH ⊓ D.QH,D.UH ⊓ i.conjugate D.QH⁆ := commutator_comm _ _
        _ ≤ ⁅i.conjugate D.UH ⊓ D.QH,D.UH⁆ := commutator_mono le_rfl inf_le_left
        _ = D.V₁ := hreverse
    · rw [←hi]
      exact commutator_mono le_rfl inf_le_left
  refine ⟨hi,hreverse,hjoin,hinf,?_,hcomm⟩
  have hnorm : i.conjugate D.V₁ ≤ normalizer (D.V₁ : Set G) :=
    ((map_mono (h.point_lt.le.trans (le_conjugateSpanBy _ _))).trans (i.large_le hb)).trans
      (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
  have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes D.V₁ (i.conjugate D.V₁) hnorm
  rw [h.point_card,hpc,hinf,card_bot,one_mul] at hh
  exact hh.symm

end CFSG.Quasithin.Chapter14.Section06
