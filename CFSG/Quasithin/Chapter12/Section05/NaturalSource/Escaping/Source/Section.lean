module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Completion
public import Theory.GroupTheory.CentralizerModulo.ConjugateSpan

/-!
# G.2.2 on the terminal point quotient

The original middle interval V₇/V₁ remains irreducible in any group between
M₁ and G₁. Characteristic two passes through the original full Sylow T,
so G.2.2 makes its normal closure in J/V₁ reduced. Consequently its
commutators with the intrinsic O₂(J) lie in V₁. Applying this to J=L₁H
supplies the terminal commutator estimate with the actual Q_H.

The source selection still has to prove M₁ ≤ L₁H; it is retained explicitly
here, rather than replaced by an assumption on the desired commutator.
Source: Aschbacher--Smith, proof of 12.5.1, printed p.822, and G.2.2.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.SL5ExteriorSquare
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

theorem seven_closure_image_reduced_in_overgroup (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (J : Subgroup G) (hMJ : s.marking.Mi 1 ≤ J) (hJG : J ≤ s.marking.Gi 1)
    {Q : Type*} [Group Q] [Finite Q]
    (q : J →* Q) (hq : Function.Surjective q)
    (hker : q.ker = (s.marking.Vi 1).subgroupOf J) :
    IsPReduced 2 (normalClosure
      (((s.marking.Vi 7).subgroupOf J).map q : Set Q)) := by
  let H := J
  let A := (L ⊓ s.marking.Gi 1) ⊔ (T : Subgroup G)
  have hTH : (T : Subgroup G) ≤ H := (le_inf le_sup_right s.sylow_le_G₁).trans hMJ
  have h7T : s.marking.Vi 7 ≤ (T : Subgroup G) :=
    (s.marking.subspace_le _).trans D.le_sylow
  have h7H := h7T.trans hTH
  have h1H : s.marking.Vi 1 ≤ H := ((s.marking.subspace_le _).trans D.le_sylow).trans hTH
  have hcharG : centralizer (pCore 2 (s.marking.Gi 1) : Set (s.marking.Gi 1)) ≤
      pCore 2 (s.marking.Gi 1) :=
    Chapter1.mem_He_iff.mp (Chapter1.twoLocal_mem_He_of_sylow_le T
      (h.simpleQTKE.evenCharacteristic T) (s.marking.Gi_twoLocal 1 (.inl rfl)) s.sylow_le_G₁)
  have hchar : centralizer (pCore 2 H : Set H) ≤ pCore 2 H :=
    (Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe hJG)).mp
      (centralizer_pCore_le_of_sylow_le (T.subtype s.sylow_le_G₁) (J.subgroupOf (s.marking.Gi 1))
        (fun _ hx => hTH hx) hcharG)
  let := D.elementary
  let : IsElementaryAbelian 2 (s.marking.Vi 7) := IsElementaryAbelian.of_le (s.marking.subspace_le _)
  let : IsElementaryAbelian 2 ((s.marking.Vi 7).subgroupOf H) :=
    IsElementaryAbelian.subgroupOf h7H
  have hNV : q.ker ≤ (s.marking.Vi 7).subgroupOf H := by
    rw [hker]
    exact comap_mono s.V₁_lt_V₇.le
  have hne : q.ker ≠ (s.marking.Vi 7).subgroupOf H := by
    rw [hker]
    intro he
    have hh := congrArg (map H.subtype) he
    rw [map_subgroupOf_eq_of_le h1H, map_subgroupOf_eq_of_le h7H] at hh
    exact s.V₁_lt_V₇.ne hh
  have hAn : A ≤ normalizer (s.marking.Vi 7 : Set G) :=
    sup_le s.point_component_normalizes_seven
      (s.sylow_normalizes_subspace V₇ flagGroup_stabilizes_standard.2.2.2.2)
  have hnorm : A.subgroupOf H ≤ normalizer ((s.marking.Vi 7).subgroupOf H : Set H) := by
    rw [← subgroupOf_normalizer_eq h7H]
    exact comap_mono hAn
  have hirr : ∀ E : Subgroup H, q.ker ≤ E → E ≤ (s.marking.Vi 7).subgroupOf H →
      A.subgroupOf H ≤ normalizer (E : Set H) →
      E = q.ker ∨ E = (s.marking.Vi 7).subgroupOf H := by
    intro E hNE hE7 hn
    have h1E : s.marking.Vi 1 ≤ E.map H.subtype := by
      rw [← map_subgroupOf_eq_of_le h1H]
      apply map_mono
      rwa [← hker]
    have hE7' : E.map H.subtype ≤ s.marking.Vi 7 := by
      simpa only [map_subgroupOf_eq_of_le h7H] using map_mono (f := H.subtype) hE7
    have hnE : L ⊓ s.marking.Gi 1 ≤ normalizer (E.map H.subtype : Set G) := by
      apply le_normalizer_iff.mpr
      rintro l hl _ ⟨v, hv, rfl⟩
      have hlJ : l ∈ J := hMJ ⟨(show L ≤ L ⊔ (T : Subgroup G) from le_sup_left) hl.1,hl.2⟩
      refine ⟨⟨l, hlJ⟩ * v * ⟨l, hlJ⟩⁻¹, ?_, rfl⟩
      exact le_normalizer_iff.mp hn ⟨l, hlJ⟩ ((show L ⊓ s.marking.Gi 1 ≤ A from le_sup_left) hl) v hv
    rcases s.marking.point_middle_invariant_interval_of_component
      (E.map H.subtype) h1E hE7' hnE with he | he
    · left
      apply map_injective H.subtype_injective
      rw [he, hker, map_subgroupOf_eq_of_le h1H]
    · right
      apply map_injective H.subtype_injective
      rw [he, map_subgroupOf_eq_of_le h7H]
  exact isPReduced_normalClosure_image_of_irreducible q
    hq ((s.marking.Vi 7).subgroupOf H)
    (A.subgroupOf H) (T.subtype hTH) hchar inferInstance hNV hne
    (by intro v hv; exact h7T hv)
    (by intro v hv; exact (show (T : Subgroup G) ≤ A from le_sup_right) hv)
    hnorm hirr


/-- The intrinsic two-core of the intermediate group centralizes the whole
seven-space closure modulo the original point. -/
theorem seven_span_commutator_core_le_point
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (J : Subgroup G) (hMJ : s.marking.Mi 1 ≤ J) (hJG : J ≤ s.marking.Gi 1) :
    ⁅conjugateSpanBy (s.marking.Vi 7) J, J.pCoreIn 2⁆ ≤ s.marking.Vi 1 := by
  let N := (s.marking.Vi 1).subgroupOf J
  have hTJ : (T : Subgroup G) ≤ J := (le_inf le_sup_right s.sylow_le_G₁).trans hMJ
  have h1J : s.marking.Vi 1 ≤ J := ((s.marking.subspace_le _).trans D.le_sylow).trans hTJ
  have h7J : s.marking.Vi 7 ≤ J := ((s.marking.subspace_le _).trans D.le_sylow).trans hTJ
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer h1J).mpr hJG
  let q : J →* J ⧸ N := QuotientGroup.mk' N
  have hr : IsPReduced 2 (((conjugateSpanBy (s.marking.Vi 7) J).subgroupOf J).map q) := by
    rw [← normalClosure_subgroupOf_eq_conjugateSpanBy _ _ h7J,
      map_normalClosure _ q (QuotientGroup.mk'_surjective N)]
    exact s.seven_closure_image_reduced_in_overgroup h J hMJ hJG q
      (QuotientGroup.mk'_surjective N) (QuotientGroup.ker_mk' N)
  have hmap : (pCore 2 J).map q ≤ pCore 2 (J ⧸ N) :=
    le_sSup ⟨Normal.map inferInstance q (QuotientGroup.mk'_surjective N),
      pCore_isPGroup.map q⟩
  have hz : ⁅((conjugateSpanBy (s.marking.Vi 7) J).subgroupOf J).map q,
      (pCore 2 J).map q⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr
      (hr.le_centralizer_pCore.trans (centralizer_le hmap))
  rw [← map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hz
  have hUJ : conjugateSpanBy (s.marking.Vi 7) J ≤ J := conjugateSpanBy_le_self h7J
  have hi : ⁅conjugateSpanBy (s.marking.Vi 7) J, J.pCoreIn 2⁆ ≤ J :=
    (Subgroup.commutator_le_sup _ _).trans (sup_le hUJ (pCoreIn_le 2 J))
  have hcore : (J.pCoreIn 2).subgroupOf J = pCore 2 J :=
    comap_map_eq_self_of_injective J.subtype_injective _
  have he := SubgroupTransport.subgroupOf_commutator (conjugateSpanBy (s.marking.Vi 7) J)
    (J.pCoreIn 2) hUJ (pCoreIn_le 2 J)
  rw [hcore] at he
  rw [← he] at hz
  have hh := map_mono (f := J.subtype) hz
  simpa only [N, map_subgroupOf_eq_of_le hi, map_subgroupOf_eq_of_le h1J] using hh

/-- The actual terminal commutator estimate. The retained incidence premise
is the source's M₁ = L₁(H ∩ M), used here only through its containment. -/
theorem terminal_commutator_line_of_point_parabolic_le
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {H : Subgroup G} (hHG : H ≤ s.marking.Gi 1)
    (hM : s.marking.Mi 1 ≤ s.marking.Li 1 ⊔ H) (g : G) :
    ⁅s.marking.UH H, terminalIntersection s.marking H g⁆ ≤ s.marking.Vi 1 := by
  exact (commutator_mono (conjugateSpanBy_mono le_rfl le_sup_right) inf_le_right).trans
    (s.seven_span_commutator_core_le_point h (s.marking.Li 1 ⊔ H) hM
      (sup_le (s.marking.Li_le_Gi 1) hHG))

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
