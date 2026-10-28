module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CyclicResidual
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.OriginalAt.Alternating.StarQuotient
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.NaturalAt

/-!
# Guarded critical geometry and cyclic-residual exclusion

Only Structural1222At at the original G,T is used.
For each J in the literal H_z, the original natural flag constructs the
F.8 critical geometry for LT and J. If R₁ lay in O₂(J), the terminal edge
would place U_J in a conjugate of that core. The exact F.8 section kernel
would then centralize the original seed modulo the terminal point,
contradicting criticality. Thus the point-parabolic image has nontrivial
two-core. Its order ratio six forces four to divide every Sylow order in
J/O₂(J), excluding a cyclic three-group two-residual.

This proves 14.7.8 for all source overgroups, not only G₁. The later
three-core reduction uses this same Sylow bound. No source Data or local
recognition hypothesis is assumed.

Source: Aschbacher–Smith, 14.7.8 and its use in 14.7.27–29,
printed pp.1045,1054–1055; F.8.7, printed p.317, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}
local notation "B" => (F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G)

/-- Construct the original F.8 hypotheses for every actual member of H_z. -/
theorem local_f8_hypothesis_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G))) :
    ChapterF.Section08.Setup.Hypothesis (F.f8SourceSetup L J) := by
  let := h.chosen.elementary
  obtain ⟨z, hz, he⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
  have hzV : z ∈ V := F.le_seed 1 (he.symm ▸ mem_zpowers z)
  apply F.f8Source_hypothesis h.source.simpleQTKE L (normalizer (L : Set G))
    (by decide) h.chosen.le_sylow h.chosen.normalizes
    (h.sylow_normalizes_at structural) h.residual
    (fun _ => ⟨h.naturalMarking⟩) rfl
    (h.maximal_unique_at structural).2
    ((Subgroup.centralizer_le_normalizer _).trans (h.seed_normalizer_le_at structural)) h.centralizer_L
    h.source.maximal_faithful.2.1.2.2 (((structural L h.source).2.2 V h.chosen).2.1)
    (h.centralizer_LT_at structural) z he hz _ hab J hJ
  intro x hx hx1
  obtain ⟨l,hl,he⟩ := h.vector_transitive hzV hx hz hx1
  exact ⟨l,h.chosen.normalizes hl,he⟩

private theorem f8_edge_core_not_le_point_core
    {D : ChapterF.Section08.Setup G} (hf : D.Hypothesis) :
    ¬ (D.L₁ ⊔ D.T).pCoreIn 2 ≤ D.QH := by
  intro hle
  obtain ⟨C⟩ := hf.exists_criticalPath
  have hcore : ⁅D.U,D.QH⁆ ≤ D.V₁ := by
    rw [hf.QH_eq_quotientCentralizer_image]
    apply commutator_le.mpr
    rintro u hu x ⟨y,hy,rfl⟩
    exact (ChapterF.Section08.Setup.mem_quotientCentralizer_iff _ _ _
      (hf.g2.U_le_H.trans hf.H_le) y).mp hy u hu
  let f := (MulAut.conj (C.g : G)).toMonoidHom
  have hm : ⁅C.Ug,D.QH.map f⁆ ≤ C.A₁ := by
    have hm := map_mono (f := f) hcore
    rwa [map_commutator] at hm
  have hU : D.U ≤ D.QH.map f := by
    have he := C.edge_cores.1
    rw [C.endpoint_edge_eq, ← map_pCoreIn_of_injective 2 _ f (MulAut.conj (C.g : G)).injective] at he
    exact he.trans (map_mono hle)
  exact C.commutator_not_le_A₁ ((commutator_mono le_rfl
    ((le_conjugateSpanBy D.V D.H).trans hU)).trans hm)

/-- The original point-parabolic core cannot lie in the core of any member of H_z. -/
theorem point_core_not_le_local_core_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G))) :
    ¬ F.Ri L 1 ≤ J.pCoreIn 2 := by
  have hf := local_f8_hypothesis_at h hab structural J hJ
  have he : (F.f8SourceSetup L J).L₁ = F.Li L 1 := by
    simp only [InvariantFlag.f8SourceSetup, ChapterG.Section02.Setup.L₁, InvariantFlag.Li,
      show ¬ (3 = 5 ∧ (1 = 2 ∨ 1 = 3)) by decide, ↓reduceIte]
    rfl
  simpa only [he, InvariantFlag.Ri, ChapterG.Section02.Setup.QH,
    InvariantFlag.f8SourceSetup] using f8_edge_core_not_le_point_core hf

/-- Every Sylow two-subgroup of each literal local star quotient has order divisible by four. -/
theorem four_dvd_local_star_sylow_card_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (S : Sylow 2 (HStar J)) : 4 ∣ Nat.card S := by
  have hBJ : B ≤ J := (local_f8_hypothesis_at h hab structural J hJ).local_le
  let f : B →* HStar J := (QuotientGroup.mk' (pCore 2 J)).comp (inclusion hBJ)
  have hk : IsPGroup 2 f.ker := by
    change IsPGroup 2 ((QuotientGroup.mk' (pCore 2 J)).ker.comap (inclusion hBJ))
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective hBJ)
  have hr := point_image_ratio_at h structural f hk
  have him : (pCore 2 B).map f.rangeRestrict ≤ pCore 2 f.range :=
    le_sSup ⟨(inferInstance : (pCore 2 B).Normal).map _ f.rangeRestrict_surjective,
      pCore_isPGroup.map _⟩
  have hne : pCore 2 f.range ≠ ⊥ := by
    intro he
    apply point_core_not_le_local_core_at h hab structural J hJ
    rintro x ⟨x,hx,rfl⟩
    have hzero : f.rangeRestrict x = 1 :=
      mem_bot.mp (he ▸ him (mem_map_of_mem _ hx))
    have hxcore : inclusion hBJ x ∈ pCore 2 J :=
      (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val hzero)
    exact mem_map_of_mem J.subtype hxcore
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := f.range)).exists_card_eq
  have hn0 : n ≠ 0 := by
    intro hz
    exact hne (eq_bot_of_card_eq _ (by simpa only [hz, pow_zero] using hn))
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hd : 4 ∣ Nat.card f.range := by
    rw [hr, hn, pow_succ]
    exact ⟨3 * 2 ^ k, by ring⟩
  exact S.pow_dvd_card_of_pow_dvd_card (n := 2)
    (hd.trans f.range.card_subgroup_dvd_card)

/-- Source 14.7.8 for every member of H_z, including proper point-normalizer subgroups. -/
theorem no_cyclic_three_local_star_residual_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G))) :
    ¬ (IsCyclic (pResidual 2 (HStar J)) ∧ IsPGroup 3 (pResidual 2 (HStar J))) := by
  rintro ⟨hc,h3⟩
  let := hc
  let S : Sylow 2 (HStar J) := Classical.choice inferInstance
  have hb := S.card_le_two_of_cyclic_three_residual (pCore_quotient_pCore_eq_bot 2) h3
  have hd := four_dvd_local_star_sylow_card_at h hab structural J hJ S
  have := Nat.le_of_dvd (Nat.card_pos (α := S)) hd
  omega

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly
