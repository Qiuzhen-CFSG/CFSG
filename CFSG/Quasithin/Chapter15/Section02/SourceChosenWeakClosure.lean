module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenSetup
public import CFSG.Quasithin.Chapter15.Section01.CentralizingControl
public import CFSG.Quasithin.ChapterE.Section03.ZeroClosure
public import CFSG.Quasithin.ChapterE.Section03.Offenders.Transport.Foundations
public import Stellmacher.ElementaryAbelianMaxFusion

/-!
# Weak closure and fusion for the actual chosen module

Maximality identifies M with the full normalizer of the nontrivial chosen
module. Thus the parameters of its actual image action are the global local
parameters, without an unmarked action comparison. The E.3.21 argument then
gives the two weak-closure conclusions of 15.2.26 from `r > 1` and the earlier
15.2.14(6) parameters.

Burnside fusion through J(T), whose normalizer is already controlled by
15.1.9, moves any conjugate containing a point of the distinguished plane to
a conjugate under Mc. Uniqueness 15.2.15 controls the point centralizer.
Containment of V in O₂(Mc) and zeroth weak closure then prove 15.2.27(3).
The proofs of `r > 1` and V ≤ O₂(Mc) remain separate source obligations.

Source: Aschbacher--Smith, 15.2.26 and the last paragraph of 15.2.27,
printed pp.1118--1119; A.1.35 and A.1.7(1) for the fusion argument.
-/

public section

open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section02

open Section01 Section03 Section03.InitialSource ChapterA.Section05To06
open ChapterD ChapterD.UniqueFactor ChapterE

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem chosen_twoCore_le_sylow (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) : twoCoreIn H ≤ (T : Subgroup G) := by
  have hp : pCore 2 H ≤ (T : Subgroup G).subgroupOf H :=
    pCore_isPGroup.le_sylow_of_normal (T.subtype hTH)
  have hm := map_mono (f := H.subtype) hp
  rw [map_subgroupOf_eq_of_le hTH] at hm
  exact hm

/-- The actual chosen module has the same full normalizer M even before the
proper-support alternative has been excluded. -/
theorem ChosenSmallSource.normalizer_eq
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V) :
    normalizer (V : Set G) = M := by
  let := h.prepared.elementary
  exact le_antisymm
    (h.maximal.1.1.2
      ⟨V, h.prepared.nontrivial, IsElementaryAbelian.isPGroup 2 V, rfl⟩
      h.prepared.normalized)
    h.prepared.normalized

/-- Identifying the full normalizer identifies both literal module parameters. -/
theorem ChosenSmallSource.local_parameters
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V) :
    letI := h.prepared.elementary
    localM V = moduleM (imageRepresentation M V h.prepared.normalized) ∧
      localA V = moduleA (imageRepresentation M V h.prepared.normalized) := by
  let := h.prepared.elementary
  have he := h.normalizer_eq
  subst M
  exact ⟨rfl, rfl⟩

/-- The numerical and weak-closure consequences of 15.2.26, retaining only
its hyperplane argument and the earlier 15.2.14(6) action parameters. -/
theorem source_chosen_weakClosure_of_globalR
    (T : Sylow 2 G) {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hr : 1 < globalR V)
    (hm : letI := h.prepared.elementary
      moduleM (imageRepresentation M V h.prepared.normalized) = 2)
    (ha : letI := h.prepared.elementary
      moduleA (imageRepresentation M V h.prepared.normalized) = 1) :
    (letI := h.prepared.elementary; 1 < globalS V) ∧
      indexedWeakClosure V (T : Subgroup G) 0 ≤
        (T : Subgroup G) ⊓ centralizer (V : Set G) ∧
      indexedWeakClosure V (twoCoreIn H) 0 ≤
        H ⊓ centralizer (conjugateSpan H V : Set G) := by
  let := h.prepared.elementary
  have hm' : localM V = 2 := h.local_parameters.1.trans hm
  have ha' : localA V = 1 := h.local_parameters.2.trans ha
  have hs : 1 < globalS V := by
    change 1 < min (globalR V) (localM V : ℕ∞)
    rw [hm']
    exact lt_min hr (by norm_num)
  have hW := weakClosure_zero_le_centralizer_of_localA_lt_globalS V
    (T : Subgroup G) (h.maximal.1.2.trans h.prepared.normalized) (ha' ▸ hs)
  have hQT := chosen_twoCore_le_sylow T H hH.1.1.2
  have hHQ : H ≤ normalizer (twoCoreIn H : Set G) := by
    simpa only [twoCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map,
      range_subtype] using (pCore 2 H).le_normalizer_map H.subtype
  refine ⟨hs, hW, ?_⟩
  rw [conjugateSpan_eq]
  exact weakClosure_le_centralizer_conjugateSpanBy V (T : Subgroup G) H
    (twoCoreIn H) 0 hQT (twoCore_le H) hHQ (hW.trans inf_le_right)

/-- Burnside fusion is supplied by the actual elementary Thompson subgroup,
not assumed as a new source premise. -/
theorem ChosenSmallSource.controls_element_fusion
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V)
    {x y : G} (hx : x ∈ V) (hy : y ∈ V) (hxy : IsConj x y) :
    ∃ n ∈ M, n * x * n⁻¹ = y := by
  have hJ : V ≤ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) :=
    le_centralizer_iff.mp (h.centralizing.trans (centralizer_le h.prepared.le_local))
  have hJT : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) :=
    sSup_le fun _ hA => hA.1
  obtain ⟨n, hn, he⟩ := T.weakly_closed_normalizer_controls_centralizer_fusion
    (elementaryAbelianMaxJ (T : Subgroup G)) hJT (maxJ_weakly_closed_normalizer T)
    (hJ hx) (hJ hy) hxy
  have hNM := (source_centralizing_baumann_control h.ambient T h.maximal
    h.centralizing).2.2.2.2.2.1
  exact ⟨n, hNM hn, he⟩

/-- Uniqueness 15.2.15 places normalizers of every nontrivial subgroup of
the distinguished plane in Mc. This uses relative, not ambient, centralizers. -/
theorem source_chosen_plane_subgroup_normalizer
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hgeo : ChosenPlaneGeometry h H ZS)
    (hu : maximalTwoLocalOvergroups (Mc ⊓ centralizer (ZS : Set G)) = {Mc})
    {A : Subgroup G} (hAZ : A ≤ ZS) (hne : A ≠ ⊥) :
    normalizer (A : Set G) ≤ Mc := by
  let := h.prepared.elementary
  apply normalizer_le_of_unique_maximalTwoLocal
    (J := Mc ⊓ centralizer (ZS : Set G))
  · intro N hN hJN
    have hn : N ∈ maximalTwoLocalOvergroups (Mc ⊓ centralizer (ZS : Set G)) :=
      ⟨hN, hJN⟩
    rw [hu] at hn
    exact Set.mem_singleton_iff.mp hn
  · exact (IsElementaryAbelian.isPGroup 2 V).to_le (hAZ.trans hgeo.plane_le)
  · exact hne
  · exact inf_le_right.trans ((centralizer_le hAZ).trans
      (Subgroup.centralizer_le_normalizer _))

/-- A point of the source plane in a conjugate permits a conjugator inside
Mc. The left-conjugation convention is preserved in the transporter. -/
theorem source_chosen_conjugate_with_plane_point
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hgeo : ChosenPlaneGeometry h H ZS)
    (hu : maximalTwoLocalOvergroups (Mc ⊓ centralizer (ZS : Set G)) = {Mc})
    (g : G) (hoverlap : ZS ⊓ V.map (MulAut.conj g).toMonoidHom ≠ ⊥) :
    ∃ c ∈ Mc, V.map (MulAut.conj g).toMonoidHom =
      V.map (MulAut.conj c).toMonoidHom := by
  obtain ⟨z, hz, hzne⟩ := (nontrivial_iff_exists_ne_one _).mp
    ((nontrivial_iff_ne_bot _).mpr hoverlap)
  obtain ⟨y, hy, hgy⟩ := hz.2
  have hyz : IsConj y z := isConj_iff.mpr ⟨g, hgy⟩
  obtain ⟨n, hn, hnz⟩ := h.controls_element_fusion hy (hgeo.plane_le hz.1) hyz
  have hc : g * n⁻¹ ∈ centralizer ({z} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    have hninv : n⁻¹ * z * n = y := by
      rw [← hnz]
      group
    have he : (g * n⁻¹) * z * (g * n⁻¹)⁻¹ = z := by
      simpa only [mul_inv_rev, inv_inv, mul_assoc] using
        (show g * (n⁻¹ * z * n) * g⁻¹ = z by rw [hninv]; exact hgy)
    exact mul_inv_eq_iff_eq_mul.mp he
  have hpoint : zpowers z ≤ ZS := zpowers_le.mpr hz.1
  have hpointne : zpowers z ≠ ⊥ := by
    intro he
    exact hzne (mem_bot.mp (he ▸ mem_zpowers z))
  have hcMc : g * n⁻¹ ∈ Mc := by
    apply source_chosen_plane_subgroup_normalizer h hgeo hu hpoint hpointne
    apply (Subgroup.centralizer_le_normalizer (zpowers z : Set G))
    rwa [zpowers_eq_closure, centralizer_closure]
  refine ⟨g * n⁻¹, hcMc, ?_⟩
  rw [← offender_map_conj_map]
  have hv : V.map (MulAut.conj n⁻¹).toMonoidHom = V :=
    mem_normalizer_iff_map_conj_eq.mp (h.prepared.normalized (M.inv_mem hn))
  rw [hv]

/-- The source overlap implication once the independent 15.2.27(2) core
argument is supplied. Both weak closure and element fusion are literal. -/
theorem source_chosen_overlap_of_core
    (T : Sylow 2 G) {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hgeo : ChosenPlaneGeometry h H ZS)
    (hu : maximalTwoLocalOvergroups (Mc ⊓ centralizer (ZS : Set G)) = {Mc})
    (hW : indexedWeakClosure V (T : Subgroup G) 0 ≤ centralizer (V : Set G))
    (hcore : V ≤ twoCoreIn Mc) :
    ∀ g : G, ZS ⊓ V.map (MulAut.conj g).toMonoidHom ≠ ⊥ →
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  have hTMc : (T : Subgroup G) ≤ Mc := hgeo.outside.1.1.2.trans hgeo.in_partner
  have hQT := chosen_twoCore_le_sylow T Mc hTMc
  have hnQ : Mc ≤ normalizer (twoCoreIn Mc : Set G) := by
    simpa only [twoCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map,
      range_subtype] using (pCore 2 Mc).le_normalizer_map Mc.subtype
  intro g hg
  obtain ⟨c, hc, he⟩ := source_chosen_conjugate_with_plane_point h hgeo hu g hg
  rw [he]
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply le_centralizer_iff.mp
  apply le_trans (gamma_le_weakClosure
    ((mem_gamma_zero_iff V (T : Subgroup G) _).mpr ⟨c, rfl, ?_⟩)) hW
  have hm := map_mono (f := (MulAut.conj c).toMonoidHom) hcore
  have hq : (twoCoreIn Mc).map (MulAut.conj c).toMonoidHom = twoCoreIn Mc :=
    mem_normalizer_iff_map_conj_eq.mp (hnQ hc)
  rw [hq] at hm
  exact hm.trans hQT

end CFSG.Quasithin.Chapter15.Section02
