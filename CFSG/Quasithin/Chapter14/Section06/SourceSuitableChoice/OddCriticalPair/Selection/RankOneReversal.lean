module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Selection.StrictDisplacement
public import Theory.Representation.BinaryOffender.InvolutionRatio

/-!
# Rank-one equality under the actual critical-endpoint reversal

F.9.17 gives a new normalized endpoint whose product with the old
representative lies in H. Conjugation exchanges both literal denominators.
When their ranks equal one, the reversed actor is cyclic of order two;
the denominator displacement estimate proves its required quadratic ratio.
The same representative returns every H-invariant label.

This supplies the reverse-point step of 14.6.13 to
qt-e-suitable-orthogonal-marking. Source: Aschbacher--Smith, F.9.17 and
14.6.13, printed pp.324 and 1032.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddCriticalPair.Selection
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter13.Section08 Chapter13.Section08.SourceCompletion Chapter13.Section08.CriticalGeometry
open Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
open PairConsequences
variable {G : Type*} [Group G] [Finite G]
variable {D : ChapterF.Section09.Setup G} {h : D.Hypothesis}
variable [IsElementaryAbelian 2 D.UH] {a : LocalQuotientAction D.H D.UH D.V₁}

/-- The denominator estimate needs only the literal endpoint, not a prior quadratic selection. -/
theorem endpoint_displacement_rank_le (i : h.CriticalEndpoint) (hb : 3 ≤ h.b)
    {t : D.H ⧸ pCore 2 D.H} (ht : t ∈ actorImage D.H (i.conjugate D.UH)) :
    Module.finrank (ZMod 2) (LinearMap.range (a.representation t - LinearMap.id)) ≤
      Nat.log 2 ((commutatorPreimage D.UH (i.conjugate D.UH)
        (i.conjugate D.V₁)).relIndex D.UH) + 1 := by
  let s := ModuleBound.OriginalF916.conjugationSection a h.H_centralizes
  let B := i.conjugate D.UH
  let C := i.conjugate D.V₁
  let E := commutatorPreimage D.UH B C
  have hUV : D.UH ≤ D.VH := conjugateSpanBy_mono h.plus_le le_rfl
  have hBH : B ≤ D.H := (map_mono hUV).trans (i.large_le hb)
  have hnorm : D.UH ≤ normalizer (C : Set G) := by
    have hn := map_mono (f := (MulAut.conj i.representative).toMonoidHom)
      (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
    rw [map_equiv_normalizer_eq] at hn
    exact (hUV.trans (i.reverse_le hb)).trans hn
  have hC : Nat.card C = 2 := by
    change Nat.card (D.V₁.map (MulAut.conj i.representative).toMonoidHom) = 2
    rw [card_map_of_injective (MulAut.conj i.representative).injective,h.point_card]
  obtain ⟨hline,hdisp⟩ := s.critical_line_displacement B C hnorm hC
  have hm : (s.image E).map (a.representation t - LinearMap.id) ≤ s.image C := by
    rintro _ ⟨v,hv,rfl⟩
    exact hdisp t ht v hv
  have hh := LinearMap.finrank_range_le_quotient_add_map
    (a.representation t - LinearMap.id) (s.image E)
  rw [s.quotient_finrank E (s.line_le_DH B C hBH)] at hh
  exact hh.trans (Nat.add_le_add_left ((Submodule.finrank_mono hm).trans hline) _)

/-- A rank-one endpoint with denominator codimension one is a genuine quadratic member. -/
theorem endpoint_quadratic_of_ranks_one (i : h.CriticalEndpoint) (hb : 3 ≤ h.b)
    (hr : rank (actorImage D.H (i.conjugate D.UH)) = 1)
    (hd : Nat.log 2 ((commutatorPreimage D.UH (i.conjugate D.UH)
      (i.conjugate D.V₁)).relIndex D.UH) = 1) :
    Reorientation.QuadraticMember a.representation (actorImage D.H (i.conjugate D.UH)) := by
  let B := actorImage D.H (i.conjugate D.UH)
  have hBH : i.conjugate D.UH ≤ D.H :=
    (map_mono (conjugateSpanBy_mono h.plus_le le_rfl)).trans (i.large_le hb)
  let : IsElementaryAbelian 2 (i.conjugate D.UH) := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 B := starImage_isElementaryAbelian D.H _ hBH
  change rank B = 1 at hr
  have hne : B ≠ ⊥ := by intro he; simp [he,rank] at hr
  have hB : IsElementaryTwo B := ⟨hne,inferInstance⟩
  have hc : Nat.card B = 2 := by simpa only [hr,pow_one] using hB.card_eq_two_pow_rank
  let : IsCyclic B := isCyclic_of_prime_card hc
  obtain ⟨t,ht⟩ := B.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
  have ho : orderOf t = 2 := by rw [← Nat.card_zpowers,ht,hc]
  have hq := (involution_actor_rank_and_fixedCodim a.representation t ho).2.2.1
  rw [ht] at hq
  refine ⟨hB,hq,?_⟩
  have hdisp := endpoint_displacement_rank_le (a := a) i hb
    (ht ▸ mem_zpowers t)
  rw [hd,← fixedCodim_zpowers_eq_displacement_rank,ht] at hdisp
  change fixedCodim a.representation B ≤ 2 * rank B
  rw [hr]
  exact hdisp

/-- Reversal retains the actual product in H, needed to change only the
right-hand representative when marking the reverse support. -/
theorem SelectedQuadraticEndpoint.reversal_with_product
    (c : SelectedQuadraticEndpoint h a) (hb : 3 ≤ h.b) :
    ∃ j : h.CriticalEndpoint, j.representative * c.endpoint.representative ∈ D.H ∧
      ∀ A : Subgroup G, D.H ≤ normalizer (A : Set G) →
        j.conjugate (c.endpoint.conjugate A) = A := by
  let i := c.endpoint
  have hsmall : D.UH ≤ D.VH := conjugateSpanBy_mono h.plus_le le_rfl
  have hn : ¬ i.conjugate D.UH ≤ D.QH := by
    intro hc
    have hs := c.strict
    rw [critical_denominator_eq h _ ((map_mono hsmall).trans (i.large_le hb)),
      inf_eq_left.mpr hc] at hs
    exact lt_irrefl _ hs
  open ChapterF.Section09.Setup.Hypothesis in
  have hn' : ¬ ChapterF.Section07.CriticalPairs.vertexModule
      (family (D := D)) h.f7Setup.seed i.vertex ≤ (family (D := D) true).pCoreIn 2 := by
    intro hc
    apply hn
    have hm := map_mono (f := (D.LT ⊔ D.H).subtype) hc
    rw [i.large_map, ← AmalgamLocalCores.pCoreIn_map_of_injective
      2 _ (D.LT ⊔ D.H).subtype_injective,
      show (family (D := D) true).map (D.LT ⊔ D.H).subtype = D.H from
        map_subgroupOf_eq_of_le le_sup_right] at hm
    exact (map_mono hsmall).trans hm
  obtain ⟨j,hprod⟩ := i.reversal (i.moving_of_not_le_core hb _ le_rfl hn')
  let k : h.CriticalEndpoint := j
  have hp : k.representative * i.representative ∈ D.H := hprod
  refine ⟨k,hp,?_⟩
  intro A hA
  change (A.conjBy i.representative).conjBy k.representative = A
  rw [← conjBy_mul]
  exact mem_normalizer_iff_map_conj_eq.mp (hA hp)

/-- Rank-one equality survives the actual F.9.17 endpoint reversal, with all
H-invariant labels returned by the same conjugator. -/
theorem SelectedQuadraticEndpoint.rank_one_reversal
    (c : SelectedQuadraticEndpoint h a) (hb : 3 ≤ h.b)
    (hr : rank (actorImage D.H (c.endpoint.conjugate D.UH)) = 1)
    (hd : Nat.log 2 ((commutatorPreimage D.UH (c.endpoint.conjugate D.UH)
      (c.endpoint.conjugate D.V₁)).relIndex D.UH) = 1) :
    ∃ r : SelectedQuadraticEndpoint h a,
      (∀ A : Subgroup G, D.H ≤ normalizer (A : Set G) →
        r.endpoint.conjugate (c.endpoint.conjugate A) = A) ∧
      r.endpoint.representative * c.endpoint.representative ∈ D.H ∧
      rank (actorImage D.H (r.endpoint.conjugate D.UH)) = 1 ∧
      Nat.log 2 ((commutatorPreimage D.UH (r.endpoint.conjugate D.UH)
        (r.endpoint.conjugate D.V₁)).relIndex D.UH) = 1 := by
  obtain ⟨j,hprod,hj⟩ := c.reversal_with_product hb
  let s := ModuleBound.OriginalF916.conjugationSection a h.H_centralizes
  have hf := f9_section_faithful D h s
  have hZ := h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)
  have hU := le_normalizer_conjugateSpanBy D.Vplus D.H
  have hUV : D.UH ≤ D.VH := conjugateSpanBy_mono h.plus_le le_rfl
  have hBH : c.endpoint.conjugate D.UH ≤ D.H := (map_mono hUV).trans (c.endpoint.large_le hb)
  have hjH : j.conjugate D.UH ≤ D.H := (map_mono hUV).trans (j.large_le hb)
  have hUC : D.UH ≤ normalizer (c.endpoint.conjugate D.V₁ : Set G) := by
    have hn := map_mono (f := (MulAut.conj c.endpoint.representative).toMonoidHom) hZ
    rw [map_equiv_normalizer_eq] at hn
    exact (hUV.trans (c.endpoint.reverse_le hb)).trans hn
  have hretU := hj D.UH hU
  have hretZ := hj D.V₁ hZ
  have hleft : j.conjugate (commutatorPreimage (c.endpoint.conjugate D.UH) D.UH D.V₁) =
      commutatorPreimage D.UH (j.conjugate D.UH) (j.conjugate D.V₁) := by
    rw [ChapterF.Section09.Setup.Hypothesis.CriticalEndpoint.conjugate,
      map_commutatorPreimage_equiv _ _ _ _ (hBH.trans hZ)]
    exact congrArg (fun A => commutatorPreimage A (j.conjugate D.UH) (j.conjugate D.V₁)) hretU
  have hright : j.conjugate (commutatorPreimage D.UH (c.endpoint.conjugate D.UH)
      (c.endpoint.conjugate D.V₁)) = commutatorPreimage (j.conjugate D.UH) D.UH D.V₁ := by
    rw [ChapterF.Section09.Setup.Hypothesis.CriticalEndpoint.conjugate,
      map_commutatorPreimage_equiv _ _ _ _ hUC]
    rw [show (c.endpoint.conjugate D.UH).map (MulAut.conj j.representative).toMonoidHom = D.UH from hretU,
      show (c.endpoint.conjugate D.V₁).map (MulAut.conj j.representative).toMonoidHom = D.V₁ from hretZ]
  have hstrictL := (map_lt_map_iff_of_injective
    (f := (MulAut.conj j.representative).toMonoidHom) (MulAut.conj j.representative).injective).mpr c.strict
  change j.conjugate _ < j.conjugate _ at hstrictL
  rw [hleft,hretU] at hstrictL
  have hstrictR := (map_lt_map_iff_of_injective
    (f := (MulAut.conj j.representative).toMonoidHom) (MulAut.conj j.representative).injective).mpr c.left_strict
  change j.conjugate _ < j.conjugate _ at hstrictR
  rw [hright] at hstrictR
  have hidxL := relIndex_map_map_of_injective (f := (MulAut.conj j.representative).toMonoidHom)
    (commutatorPreimage (c.endpoint.conjugate D.UH) D.UH D.V₁)
    (c.endpoint.conjugate D.UH) (MulAut.conj j.representative).injective
  change (j.conjugate _).relIndex (j.conjugate _) = _ at hidxL
  rw [hleft,hretU] at hidxL
  have hidxR := relIndex_map_map_of_injective (f := (MulAut.conj j.representative).toMonoidHom)
    (commutatorPreimage D.UH (c.endpoint.conjugate D.UH) (c.endpoint.conjugate D.V₁))
    D.UH (MulAut.conj j.representative).injective
  change (j.conjugate _).relIndex (j.conjugate _) = _ at hidxR
  rw [hright] at hidxR
  have hjr : rank (actorImage D.H (j.conjugate D.UH)) = 1 := by
    change Nat.log 2 (Nat.card (Source.starImage D.H (j.conjugate D.UH))) = 1
    rw [← s.Dgamma_relIndex _ hjH hf]
    exact (congrArg (Nat.log 2) hidxR).trans hd
  have hjd : Nat.log 2 ((commutatorPreimage D.UH (j.conjugate D.UH)
      (j.conjugate D.V₁)).relIndex D.UH) = 1 := by
    rw [hidxL]
    change Nat.log 2 ((Source.Dgamma _ _ _).relIndex _) = 1
    rw [s.Dgamma_relIndex _ hBH hf]
    exact hr
  exact ⟨⟨j,hstrictL,hstrictR,by rw [hjr,hjd],
    endpoint_quadratic_of_ranks_one j hb hjr hjd⟩,hj,hprod,hjr,hjd⟩

end CFSG.Quasithin.Chapter14.Section06.OddCriticalPair.Selection
