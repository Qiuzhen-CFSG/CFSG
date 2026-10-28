module

public import CFSG.Quasithin.ChapterG.Section02.Setup
public import CFSG.Quasithin.ChapterA.Section01.Fitting.Characteristic
public import Theory.GroupTheory.ReducedNormal.IrreducibleClosure
public import Theory.Frattini.PGroup
public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.PGroup.OmegaAmbient
/-!
# The central closure in G.2.2

Under the genuine Hypothesis G.2.1, the H-closure of V has a two-reduced
image in the literal quotient N_G(V₁)/V₁. We apply the irreducible-closure
theorem to the surjection from H onto its image in that quotient. Its kernel
is precisely the embedded V₁, and its invariant interval is the one in Setup.

The quotient two-core is the image of O₂(H). Reducedness therefore places
Ũ in the embedded Ω₁(Z(Q̃_H)). The elementary quotient kills Φ(U), while
the elementary kernel makes U a two-group. Normality in H then puts U in
its specified Sylow T, with normality relative to T.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma G.2.2, printed p.332, PDF p.343. No central containment,
reducedness, or other conclusion of that lemma is an extra premise.
-/

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G] {D : Setup G}

private def closureToTilde (h : D.BaseHypothesis) : D.H →* D.tilde D.H where
  toFun x := ⟨QuotientGroup.mk' (D.V₁.subgroupOf D.G₁) ⟨x, h.H_le x.property⟩,
    ⟨⟨x, h.H_le x.property⟩, x.property, rfl⟩⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul (QuotientGroup.mk' (D.V₁.subgroupOf D.G₁))
    (⟨x, h.H_le x.property⟩ : D.G₁) ⟨y, h.H_le y.property⟩)

private theorem closureToTilde_surjective (h : D.BaseHypothesis) :
    Function.Surjective (closureToTilde h) := by
  rintro ⟨y, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

private theorem closureToTilde_ker (h : D.BaseHypothesis) :
    (closureToTilde h).ker = D.V₁.subgroupOf D.H := by
  ext x
  change closureToTilde h x = 1 ↔ x.val ∈ D.V₁
  rw [Subtype.ext_iff]
  exact QuotientGroup.eq_one_iff (⟨x, h.H_le x.property⟩ : D.G₁)

private theorem closureToTilde_map (h : D.BaseHypothesis) (A : Subgroup G) (ha : A ≤ D.H) :
    (A.subgroupOf D.H).map (closureToTilde h) = (D.tilde A).subgroupOf (D.tilde D.H) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, h.H_le x.property⟩, hx, rfl⟩
  · rintro ⟨x, hx, hxy⟩
    exact ⟨⟨x, ha hx⟩, hx, Subtype.ext hxy⟩

private theorem closure_intrinsic (h : D.BaseHypothesis) :
    normalClosure (D.V.subgroupOf D.H : Set D.H) = D.U.subgroupOf D.H := by
  let : (D.U.subgroupOf D.H).Normal := h.U_normal
  apply le_antisymm
  · exact normalClosure_le_normal (fun x hx => le_conjugateSpanBy _ _ hx)
  · let C := normalClosure (D.V.subgroupOf D.H : Set D.H)
    have hV : D.V ≤ C.map D.H.subtype := by
      intro v hv
      have hvH := h.V_le_T.trans (le_sup_right.trans h.local_le) hv
      exact ⟨⟨v, hvH⟩, le_normalClosure hv, rfl⟩
    have hn : D.H ≤ normalizer (C.map D.H.subtype : Set G) := by
      apply le_normalizer_iff.mpr
      rintro g hg _ ⟨x, hx, rfl⟩
      exact ⟨⟨g, hg⟩ * x * ⟨g, hg⟩⁻¹, (inferInstance : C.Normal).conj_mem x hx ⟨g, hg⟩, rfl⟩
    intro u hu
    obtain ⟨c, hc, he⟩ := conjugateSpanBy_le hV hn hu
    exact D.H.subtype_injective he ▸ hc

private theorem closure_irreducible (h : D.Hypothesis) :
    ∀ E : Subgroup D.H, (D.V₁.subgroupOf D.H) ≤ E → E ≤ D.V.subgroupOf D.H →
      ((D.L₁ ⊔ D.T).subgroupOf D.H) ≤ normalizer (E : Set D.H) →
      E = D.V₁.subgroupOf D.H ∨ E = D.V.subgroupOf D.H := by
  intro E hN hV hn
  have hVH : D.V ≤ D.H := h.V_le_T.trans (le_sup_right.trans h.local_le)
  have hNH : D.V₁ ≤ D.H := h.point_le.trans hVH
  have hNE : D.V₁ ≤ E.map D.H.subtype := by
    rw [← map_subgroupOf_eq_of_le hNH]
    exact map_mono hN
  have hEV : E.map D.H.subtype ≤ D.V := by
    simpa only [map_subgroupOf_eq_of_le hVH] using map_mono (f := D.H.subtype) hV
  have hnE : D.L₁ ⊔ D.T ≤ normalizer (E.map D.H.subtype : Set G) := by
    apply le_normalizer_iff.mpr
    rintro a ha _ ⟨e, he, rfl⟩
    refine ⟨⟨a, h.local_le ha⟩ * e * ⟨a, h.local_le ha⟩⁻¹, ?_, rfl⟩
    exact le_normalizer_iff.mp hn ⟨a, h.local_le ha⟩ ha e he
  rcases h.irreducible (E.map D.H.subtype) hNE hEV hnE with hh | hh
  · left
    apply map_injective D.H.subtype_injective
    simpa only [map_subgroupOf_eq_of_le hNH] using hh
  · right
    apply map_injective D.H.subtype_injective
    simpa only [map_subgroupOf_eq_of_le hVH] using hh

/-- G.2.2(4), with the literal tilde image and its centralizer in H̃. -/
public theorem Hypothesis.tilde_U_reduced (h : D.Hypothesis) :
    IsPReduced 2 ((D.tilde D.U).subgroupOf (D.tilde D.H)) := by
  let b := h.toBaseHypothesis
  let f := closureToTilde b
  have hf := closureToTilde_surjective b
  have hVH : D.V ≤ D.H := h.V_le_T.trans (le_sup_right.trans h.local_le)
  have hNH : D.V₁ ≤ D.H := h.point_le.trans hVH
  have hTH : D.T ≤ D.H := le_sup_right.trans h.local_le
  obtain ⟨P, hP⟩ := h.sylow_H
  have hPT : (P : Subgroup D.H) = D.T.subgroupOf D.H := by
    apply map_injective D.H.subtype_injective
    rw [hP, map_subgroupOf_eq_of_le hTH]
  have hNV : f.ker ≤ D.V.subgroupOf D.H := by
    rw [closureToTilde_ker]
    exact comap_mono h.point_le
  have hne : f.ker ≠ D.V.subgroupOf D.H := by
    rw [closureToTilde_ker]
    intro he
    have hm := congrArg (map D.H.subtype) he
    rw [map_subgroupOf_eq_of_le hNH, map_subgroupOf_eq_of_le hVH] at hm
    exact h.quotient_nonzero hm
  have hVP : D.V.subgroupOf D.H ≤ P := by
    rw [hPT]
    exact comap_mono h.V_le_T
  have hPA : (P : Subgroup D.H) ≤ (D.L₁ ⊔ D.T).subgroupOf D.H := by
    rw [hPT]
    exact comap_mono le_sup_right
  have hAV : (D.L₁ ⊔ D.T).subgroupOf D.H ≤ normalizer (D.V.subgroupOf D.H : Set D.H) := by
    rw [← subgroupOf_normalizer_eq hVH]
    exact comap_mono h.local_normalizes_V
  have hirr : ∀ E : Subgroup D.H, f.ker ≤ E → E ≤ D.V.subgroupOf D.H →
      ((D.L₁ ⊔ D.T).subgroupOf D.H) ≤ normalizer (E : Set D.H) →
      E = f.ker ∨ E = D.V.subgroupOf D.H := by
    rw [closureToTilde_ker]
    exact closure_irreducible h
  let := h.elementary
  have hr := isPReduced_normalClosure_image_of_irreducible f hf
    (D.V.subgroupOf D.H) ((D.L₁ ⊔ D.T).subgroupOf D.H) P
    ((CFSG.Quasithin.ChapterA.generalizedFitting_eq_pCore_iff 2).mp h.characteristic_two)
    (IsElementaryAbelian.subgroupOf hVH) hNV hne hVP hPA hAV hirr
  change IsPReduced 2 (normalClosure ((D.V.subgroupOf D.H).map f : Set (D.tilde D.H))) at hr
  rw [coe_map, ← map_normalClosure _ f hf, closure_intrinsic b, closureToTilde_map b D.U b.U_le_H] at hr
  exact hr

omit [Finite G] in
private theorem tilde_mono {A B : Subgroup G} (h : A ≤ B) : D.tilde A ≤ D.tilde B :=
  map_mono (comap_mono h)

private theorem tilde_core (h : D.BaseHypothesis) :
    D.tilde D.QH = (pCore 2 (D.tilde D.H)).map (D.tilde D.H).subtype := by
  let f := closureToTilde h
  let := h.elementary
  let : IsElementaryAbelian 2 D.V₁ := IsElementaryAbelian.of_le h.point_le
  have hk : IsPGroup 2 f.ker := by
    rw [closureToTilde_ker]
    exact (IsElementaryAbelian.isPGroup 2 D.V₁).comap_subtype
  have hpre := f.comap_pCore_of_ker_isPGroup (closureToTilde_surjective h) hk
  have hm : (pCore 2 D.H).map f = pCore 2 (D.tilde D.H) := by
    rw [← hpre, map_comap_eq_self_of_surjective (closureToTilde_surjective h)]
  have hQ : D.QH.subgroupOf D.H = pCore 2 D.H := by
    change ((pCore 2 D.H).map D.H.subtype).comap D.H.subtype = _
    exact comap_map_eq_self_of_injective D.H.subtype_injective _
  rw [← hQ, closureToTilde_map h D.QH (pCoreIn_le 2 D.H)] at hm
  rw [← hm]
  exact (map_subgroupOf_eq_of_le (tilde_mono (D := D) (pCoreIn_le 2 D.H))).symm

/-- The elementary abelianness asserted by the central containment in G.2.2(1). -/
public theorem Hypothesis.tilde_U_elementary (h : D.Hypothesis) :
    IsElementaryAbelian 2 (D.tilde D.U) := by
  let := h.tilde_U_reduced.elementary
  have he := IsElementaryAbelian.map (p := 2) (A := (D.tilde D.U).subgroupOf (D.tilde D.H))
    (D.tilde D.H).subtype
  rwa [map_subgroupOf_eq_of_le (tilde_mono h.U_le_H)] at he

/-- G.2.2(1), with the center and omega subgroup embedded into N_G(V₁)/V₁. -/
public theorem Hypothesis.tilde_U_central (h : D.Hypothesis) :
    D.tilde D.V ≤ D.tilde D.U ∧
      D.tilde D.U ≤ omegaOneAmbient ((center (D.tilde D.QH)).map (D.tilde D.QH).subtype) := by
  refine ⟨tilde_mono (le_conjugateSpanBy _ _), ?_⟩
  have hr := h.tilde_U_reduced
  have hUH : D.tilde D.U ≤ D.tilde D.H := tilde_mono h.U_le_H
  have hc : D.tilde D.U ≤ (center (D.tilde D.QH)).map (D.tilde D.QH).subtype := by
    intro u hu
    have huQ : u ∈ D.tilde D.QH := by
      rw [tilde_core h.toBaseHypothesis]
      exact mem_map_of_mem (D.tilde D.H).subtype
        (hr.le_pCore (show (⟨u, hUH hu⟩ : D.tilde D.H) ∈
          (D.tilde D.U).subgroupOf (D.tilde D.H) from hu))
    refine ⟨⟨u, huQ⟩, mem_center_iff.mpr ?_, rfl⟩
    intro q
    have hq := (tilde_core h.toBaseHypothesis).le q.property
    obtain ⟨q', hq', hqeq⟩ := hq
    apply Subtype.ext
    have he := congrArg Subtype.val (hr.le_centralizer_pCore
      (show (⟨u, hUH hu⟩ : D.tilde D.H) ∈
        (D.tilde D.U).subgroupOf (D.tilde D.H) from hu) q' hq')
    change (q' : D.Tilde) = (q : D.Tilde) at hqeq
    change (q' : D.Tilde) * u = u * (q' : D.Tilde) at he
    change (q : D.Tilde) * u = u * (q : D.Tilde)
    rwa [hqeq] at he
  let := h.tilde_U_elementary
  rw [← omegaOneAmbient_eq_self (D.tilde D.U)]
  exact omegaOneAmbient_mono hc

private def closureQuotient (h : D.BaseHypothesis) : D.U →* D.tilde D.U where
  toFun x := ⟨QuotientGroup.mk' (D.V₁.subgroupOf D.G₁) ⟨x, h.H_le (h.U_le_H x.property)⟩,
    ⟨⟨x, h.H_le (h.U_le_H x.property)⟩, x.property, rfl⟩⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul (QuotientGroup.mk' (D.V₁.subgroupOf D.G₁))
    (⟨x, h.H_le (h.U_le_H x.property)⟩ : D.G₁) ⟨y, h.H_le (h.U_le_H y.property)⟩)

private theorem closureQuotient_surjective (h : D.BaseHypothesis) :
    Function.Surjective (closureQuotient h) := by
  rintro ⟨y, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

private theorem closureQuotient_eq_one (h : D.BaseHypothesis) (u : D.U) :
    closureQuotient h u = 1 ↔ u.val ∈ D.V₁ := by
  rw [Subtype.ext_iff]
  exact QuotientGroup.eq_one_iff (⟨u, h.H_le (h.U_le_H u.property)⟩ : D.G₁)

/-- G.2.2(2): the intrinsic Frattini subgroup is embedded into G. -/
public theorem Hypothesis.frattini_U_le_point (h : D.Hypothesis) :
    (frattini D.U).map D.U.subtype ≤ D.V₁ := by
  let := h.tilde_U_elementary
  let : Fact (IsPGroup 2 (D.tilde D.U)) := ⟨IsElementaryAbelian.isPGroup 2 _⟩
  have hphi := frattini_le_comap_frattini_of_surjective (closureQuotient_surjective h.toBaseHypothesis)
  rw [frattini_eq_bot_of_isElementaryAbelian (R := D.tilde D.U) (p := 2)] at hphi
  rintro _ ⟨u, hu, rfl⟩
  exact (closureQuotient_eq_one h.toBaseHypothesis u).mp (hphi hu)

/-- The closure is a two-group; each element has fourth power one. -/
public theorem Hypothesis.U_isPGroup (h : D.Hypothesis) : IsPGroup 2 D.U := by
  let f := closureQuotient h.toBaseHypothesis
  let := h.tilde_U_elementary
  let := h.elementary
  intro u
  have he : f (u ^ 2) = 1 := by
    rw [map_pow]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (D.tilde D.U)) (f u)
  have hu : (u.val ^ 2) ∈ D.V₁ := (closureQuotient_eq_one h.toBaseHypothesis (u ^ 2)).mp he
  refine ⟨2, Subtype.ext ?_⟩
  change u.val ^ (2 ^ 2) = 1
  rw [show 2 ^ 2 = 2 * 2 from rfl, pow_mul]
  exact elemPow_eq_one_of_isElementaryAbelian _ (h.point_le hu)

/-- G.2.2(3): containment and normality are relative to the specified T. -/
public theorem Hypothesis.U_normal_in_T (h : D.Hypothesis) :
    D.U ≤ D.T ∧ (D.U.subgroupOf D.T).Normal := by
  obtain ⟨P, hP⟩ := h.sylow_H
  have hUQ : D.U ≤ D.QH := le_pCoreIn_of_normalizes h.U_isPGroup h.U_le_H
    (le_normalizer_conjugateSpanBy D.V D.H)
  have hUT : D.U ≤ D.T := hUQ.trans ((pCoreIn_le_sylow D.H P).trans hP.le)
  exact ⟨hUT, (normal_subgroupOf_iff_le_normalizer hUT).mpr
    ((le_sup_right.trans h.local_le).trans (le_normalizer_conjugateSpanBy D.V D.H))⟩

/-- All four clauses of Aschbacher–Smith G.2.2 from Hypothesis G.2.1. -/
public theorem lemma_G_2_2 (h : D.Hypothesis) :
    (D.tilde D.V ≤ D.tilde D.U ∧
      D.tilde D.U ≤ omegaOneAmbient ((center (D.tilde D.QH)).map (D.tilde D.QH).subtype)) ∧
    (frattini D.U).map D.U.subtype ≤ D.V₁ ∧
    (D.U ≤ D.T ∧ (D.U.subgroupOf D.T).Normal) ∧
    IsPReduced 2 ((D.tilde D.U).subgroupOf (D.tilde D.H)) :=
  ⟨h.tilde_U_central, h.frattini_U_le_point, h.U_normal_in_T, h.tilde_U_reduced⟩

end CFSG.Quasithin.ChapterG.Section02.Setup
