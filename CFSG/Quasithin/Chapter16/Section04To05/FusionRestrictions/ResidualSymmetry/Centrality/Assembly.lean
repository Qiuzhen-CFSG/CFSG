module

public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Centrality.Transport
public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Centrality.LieRows
public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Centrality.OtherRows
public import CFSG.KnownSimple.CarrierCatalogue
public import Mathlib.Data.List.TFAE

/-!
# The four two-centrality clauses of 16.5.6(4)

The common residual gives an isomorphism of the two full modified residuals
after conjugating the opposite actor back into the original normalizer.
The proved Lie and odd/sporadic row comparisons then preserve two-centrality.
Transport through the actual action quotients keeps both central kernels.

The chosen central involution and the earlier equality R = T_C^g supply
involutions in both actors, so the existential and universal clauses are
equivalent. The intrinsic tables, covering clauses, earlier exclusions and
common-residual identities remain explicit earlier source inputs; this is
not the completed Even Type theorem.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
Lemma 16.5.6(4), printed p.1197, using 16.1.2--5 and 16.4.11.
-/

public section

namespace CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Centrality

open Subgroup Theory.GroupTheory OtherPreliminaries
open OuterReduction.CoverFusion

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G}

/-- The complete earlier E2 alternatives give the comparison of full modified
residuals. Neither residual is replaced by its image modulo the center. -/
theorem twoCentral_iff_of_modifiedResidual_equiv [IsQuasisimple L]
    (lieTables : LieRows.EarlierTables) (otherTables : OtherRows.EarlierTables)
    (covers : LieRows.CoveringInputs L) (hcent : SourceCenterAlternative L)
    (hodd : pPrimeCore 2 L = ⊥) (hfamily : IsEvenTypeComponent L)
    (hB : ¬ ClassificationModels.IsBenderModel (L ⧸ center L))
    (hA6 : ¬ Nonempty (L ≃* alternatingGroup (Fin 6)))
    (hfour : ¬ ClassicalGroup.IsPSL (L ⧸ center L) 3 4)
    (u v : normalizer (L : Set G))
    (hu : orderOf (u : G) = 2) (hv : orderOf (v : G) = 2)
    (huq : orderOf (actionMap (L := L) le_rfl u) = 2)
    (hvq : orderOf (actionMap (L := L) le_rfl v) = 2)
    (e : modifiedCentralizerResidual L (u : G) ≃*
      modifiedCentralizerResidual L (v : G)) :
    IsTwoCentralIn (componentImage L) (actionMap le_rfl u) ↔
      IsTwoCentralIn (componentImage L) (actionMap le_rfl v) := by
  rcases hfamily with hLie | hOther
  · constructor
    · intro hc
      by_contra hn
      exact LieRows.separation lieTables covers hodd hLie hB hA6 hfour
        u v hu hv huq hvq hc hn ⟨e⟩
    · intro hc
      by_contra hn
      exact LieRows.separation lieTables covers hodd hLie hB hA6 hfour
        v u hv hu hvq huq hc hn ⟨e.symm⟩
  · exact OtherRows.twoCentral_iff_of_residualEquiv otherTables hodd hcent
      hB hfour hOther u v hu hv huq hvq e

private theorem twoCentral_actionQuotientEquiv_iff
    (e : G ≃* G) (q : ActionQuotient L) :
    IsTwoCentralIn (componentImage (L.map e.toMonoidHom))
        (actionQuotientEquiv L e q) ↔
      IsTwoCentralIn (componentImage L) q := by
  constructor
  · intro h
    have hh := twoCentral_map h (actionQuotientEquiv L e).symm
    have hm : (componentImage (L.map e.toMonoidHom)).map
        (actionQuotientEquiv L e).symm.toMonoidHom = componentImage L :=
      by
        have hc : (actionQuotientEquiv L e).symm.toMonoidHom.comp
            (actionQuotientEquiv L e).toMonoidHom = MonoidHom.id _ := by
          ext x
          exact (actionQuotientEquiv L e).symm_apply_apply x
        rw [← actionQuotientEquiv_componentImage L e, map_map, hc, map_id]
    simpa only [hm, MulEquiv.symm_apply_apply] using hh
  · intro h
    have hh := twoCentral_map h (actionQuotientEquiv L e)
    rwa [actionQuotientEquiv_componentImage] at hh

/-- Source 16.5.6(4), conditional on its actual earlier tables, covering
clauses, exclusions and common-residual identities. The two opposite action
maps remain faithful; involutions in their images are lifted before the row
comparison. No normalization of the common residual by g is assumed. -/
theorem source_lemma_16_5_6_four
    {T : Sylow 2 G} {z g : G} {R X : Subgroup G}
    (hG : Hypothesis1611 KnownSimple.IsKnownSimple G)
    (h : IntersectionSetup T z L g R)
    (htransport : R = (commutingSylow T L).conjBy g)
    (lieTables : LieRows.EarlierTables) (otherTables : OtherRows.EarlierTables)
    (covers : LieRows.CoveringInputs L) (hcent : SourceCenterAlternative L)
    (hB : ¬ ClassificationModels.IsBenderModel (L ⧸ center L))
    (hA6 : ¬ Nonempty (L ≃* alternatingGroup (Fin 6)))
    (hfour : ¬ ClassicalGroup.IsPSL (L ⧸ center L) 3 4)
    (hnormalC : commutingSylow T L ≤ normalizer (L.conjBy g : Set G))
    (hfaithC : commutingSylow T L ⊓ centralizer (L.conjBy g : Set G) = ⊥)
    (hcommonR : ∀ u ∈ R, orderOf u = 2 → modifiedCentralizerResidual L u = X)
    (hcommonC : ∀ i ∈ commutingSylow T L, orderOf i = 2 →
      modifiedCentralizerResidual (L.conjBy g) i = X) :
    List.TFAE [
      (∃ u ∈ (actionMap (h.le_sylow.trans h.sylow_normalizes)).range,
        IsTwoCentralIn (componentImage L) u),
      (∀ i ∈ (actionMap hnormalC).range, orderOf i = 2 →
        IsTwoCentralIn (componentImage (L.conjBy g)) i),
      (∃ i ∈ (actionMap hnormalC).range,
        IsTwoCentralIn (componentImage (L.conjBy g)) i),
      (∀ u ∈ (actionMap (h.le_sylow.trans h.sylow_normalizes)).range, orderOf u = 2 →
        IsTwoCentralIn (componentImage L) u)] := by
  let : IsQuasisimple L := h.component.quasisimple
  have hodd : pPrimeCore 2 L = ⊥ := by
    have hc := Subgroup.IsSubnormal.pPrimeCore_eq_bot (hG.evenType.oddCore z h.involution)
      (L.subgroupOf (involutionCentralizer z)) h.component.2.1
    have hm := pPrimeCore_map_iso 2 (subgroupOfEquivOfLe h.component.1)
    simpa only [hc, Subgroup.map_bot] using hm.symm
  have hfamily := hG.evenType.components z L h.involution h.component
  have hnormalR := h.le_sylow.trans h.sylow_normalizes
  have hfaithR : R ⊓ centralizer (L : Set G) = ⊥ := by
    let K := centralizer (L : Set G)
    have hg : g ∉ normalizer (K : Set G) := by
      intro hg
      exact h.mem_delta.2.1 (mem_normalizer_iff_map_conj_eq.mp hg)
    have hoddK := h.tight.2 g hg
    have hp : IsPGroup 2 ↥(R ⊓ K) := h.sylow.isPGroup.to_le inf_le_left
    have hle : R ⊓ K ≤ K ⊓ K.map (MulAut.conj g).toMonoidHom :=
      le_inf inf_le_right (inf_le_left.trans (h.sylow.le.trans inf_le_left))
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
    have hc : (Nat.card ↥(R ⊓ K)).Coprime
        (Nat.card ↥(K ⊓ K.map (MulAut.conj g).toMonoidHom)) := by
      rw [hn]
      exact hoddK.coprime_two_left.pow_left n
    have hb := (Subgroup.disjoint_of_coprime_natCard hc).eq_bot
    rwa [inf_eq_left.mpr hle] at hb
  have hpair (u : R) (i : commutingSylow T L)
      (hu : orderOf (u : G) = 2) (hi : orderOf (i : G) = 2) :
      IsTwoCentralIn (componentImage L) (actionMap hnormalR u) ↔
        IsTwoCentralIn (componentImage (L.conjBy g)) (actionMap hnormalC i) := by
    let a : normalizer (L : Set G) := ⟨u, hnormalR u.property⟩
    let b : normalizer (L.conjBy g : Set G) := ⟨i, hnormalC i.property⟩
    let v : normalizer (L : Set G) := (normalizerEquiv L (MulAut.conj g)).symm b
    have hv : (v : G) = MulAut.conj g⁻¹ (i : G) := by
      change (MulAut.conj g).symm (i : G) = _
      simp only [MulAut.conj_symm_apply, MulAut.conj_apply, inv_inv]
    have hv2 : orderOf (v : G) = 2 := by
      rw [hv, (MulAut.conj g⁻¹).orderOf_eq]
      exact hi
    have hq : actionQuotientEquiv L (MulAut.conj g) (actionMap (L := L) le_rfl v) =
        actionMap hnormalC i := by
      calc
        _ = actionMap (L := L.conjBy g) le_rfl (normalizerEquiv L (MulAut.conj g) v) := rfl
        _ = actionMap (L := L.conjBy g) le_rfl b :=
          congrArg (actionMap (L := L.conjBy g) le_rfl)
            ((normalizerEquiv L (MulAut.conj g)).apply_symm_apply b)
        _ = _ := rfl
    have haq : orderOf (actionMap (L := L) le_rfl a) = 2 :=
      (actionMap_orderOf hnormalR hfaithR u).trans hu
    have hvq : orderOf (actionMap (L := L) le_rfl v) = 2 := by
      rw [← (actionQuotientEquiv L (MulAut.conj g)).orderOf_eq
        (actionMap (L := L) le_rfl v), hq]
      exact (actionMap_orderOf hnormalC hfaithC i).trans hi
    have he : modifiedCentralizerResidual L (a : G) ≃*
        modifiedCentralizerResidual L (v : G) := by
      rw [hv]
      exact residualEquiv_of_common (hcommonR u u.property hu) (hcommonC i i.property hi)
    have hc := twoCentral_iff_of_modifiedResidual_equiv lieTables otherTables covers
      hcent hodd hfamily hB hA6 hfour a v hu hv2 haq hvq he
    have ht := twoCentral_actionQuotientEquiv_iff (L := L) (MulAut.conj g)
      (actionMap (L := L) le_rfl v)
    rw [hq] at ht
    exact hc.trans ht.symm
  have hz : z ∈ commutingSylow T L := by
    refine ⟨h.mem_sylow, ?_⟩
    exact mem_centralizer_iff.mpr fun x hx =>
      mem_centralizer_singleton_iff.mp (h.component.1 hx)
  let i₀ : commutingSylow T L := ⟨z, hz⟩
  let u₀ : R := ⟨MulAut.conj g z,
    htransport ▸ mem_map_of_mem (MulAut.conj g).toMonoidHom hz⟩
  have hi₀ : orderOf (i₀ : G) = 2 := h.involution
  have hu₀ : orderOf (u₀ : G) = 2 := ((MulAut.conj g).orderOf_eq z).trans h.involution
  rw [exists_twoCentral_image_iff hnormalR hfaithR,
    forall_twoCentral_image_iff hnormalC hfaithC,
    exists_twoCentral_image_iff hnormalC hfaithC,
    forall_twoCentral_image_iff hnormalR hfaithR]
  let A := ∃ u : R, orderOf (u : G) = 2 ∧
    IsTwoCentralIn (componentImage L) (actionMap hnormalR u)
  let B := ∀ i : commutingSylow T L, orderOf (i : G) = 2 →
    IsTwoCentralIn (componentImage (L.conjBy g)) (actionMap hnormalC i)
  let C := ∃ i : commutingSylow T L, orderOf (i : G) = 2 ∧
    IsTwoCentralIn (componentImage (L.conjBy g)) (actionMap hnormalC i)
  let D := ∀ u : R, orderOf (u : G) = 2 →
    IsTwoCentralIn (componentImage L) (actionMap hnormalR u)
  change List.TFAE [A, B, C, D]
  have hAB : A → B := by
    rintro ⟨u, hu, hc⟩ i hi
    exact (hpair u i hu hi).mp hc
  have hBC : B → C := fun hb => ⟨i₀, hi₀, hb i₀ hi₀⟩
  have hCD : C → D := by
    rintro ⟨i, hi, hc⟩ u hu
    exact (hpair u i hu hi).mpr hc
  have hDA : D → A := fun hd => ⟨u₀, hu₀, hd u₀ hu₀⟩
  exact List.tfae_cons_cons.mpr ⟨⟨hAB, fun hb => hDA (hCD (hBC hb))⟩,
    List.tfae_cons_cons.mpr ⟨⟨hBC, fun hc => hAB (hDA (hCD hc))⟩,
      List.tfae_cons_cons.mpr ⟨⟨hCD, fun hd => hBC (hAB (hDA hd))⟩,
        List.tfae_singleton D⟩⟩⟩

end CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Centrality
