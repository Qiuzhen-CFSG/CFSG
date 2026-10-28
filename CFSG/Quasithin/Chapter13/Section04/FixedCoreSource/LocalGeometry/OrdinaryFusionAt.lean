module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.OrdinaryBaumannAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.OmegaResidualAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.OrdinaryFusion
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.FixedModuleAt

/-!
# Ordinary ambient fusion using earlier inputs only at G,T

The literal omega-centralizer residual identifies the first parabolic.
Its two-core is normalized by N_G(T), so the augmentation Baumann
alternative gives N_G(T) <= N_G(L); the short branch uses the actual
alternating block constructed from the five-dimensional coordinates.
L-conjugators to omega representatives and Burnside fusion then give
N_G(V)-control of ambient fusion in the original full module.

The structural and escaping-vector chains both use their guarded At
inputs throughout, including the MS construction in OrdinaryBaumannAt.
The final application starts with the original nonzero fixed part,
constructs Hypothesis1223 and CoreMarking from the guarded 13.3.2 inputs,
and proves the full fusion clause. The ordinary quotient and independent
natural large-distance theorem remain explicit. This does not close
13.4.1, the covered row, or the remaining recognition adaptations.

Source: Aschbacher--Smith A.1.35, 13.2.2(5,7),13.4.2(3),13.4.3,
printed pp.30,877--878,897.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Nonsolvable Solvable
open Section08.TransvectionRecognition.Component.ModelExtension
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural AlternatingSixReconstruction.Natural.Exhaustion
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Theory.SpecificGroups.SymmetricSix.BinaryFlags (pointCore)
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original ordinary augmentation alternative controls the full Sylow normalizer. -/
theorem ordinary_sylow_normalizer_at
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (earlier : Theorem12213At KnownSimple.IsKnownSimple T)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨z,_,hz,hzL,_⟩ := exists_nonfixed_omega_escape_at h₀ h structural D m earlier
  have he := ordinary_omega_residual_at h₀ h structural D m earlier eL z hz hzL
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  have hnC : normalizer (T : Set G) ≤ normalizer (centralizer (Z : Set G) : Set G) := by
    simpa only [omegaCenterIn_eq_omegaOneAmbient, Z, omegaOneCenterAmbient] using
      (RecognitionSource.FusionReducibleNormalizer.sylow_normalizer_normalizes_omega_centralizer
        (T := T))
  have hnJ : normalizer (T : Set G) ≤ normalizer (firstCentralizerResidual L z.val : Set G) := by
    rw [←he]
    exact hnC.trans (normalizer_le_normalizer_characteristic_image _ (primeToResidual 3 _))
  let R := (firstCentralizerResidual L z.val ⊔ (T : Subgroup G)).pCoreIn 2
  have hnR : normalizer (T : Set G) ≤ normalizer (R : Set G) :=
    ((le_inf hnJ le_rfl).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)).trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  rcases ordinary_augmentation_baumann_alternative_of_largeDistance_at
      hl h structural D m eL z hz hzL with hbound | hb
  · exact (hnR.trans (normalizer_le_normalizer_baumann R)).trans hbound
  · exact sylow_normalizer_le_of_short_core h D m hb

private theorem omega_conjugate_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D) (v : V) :
    ∃ z : V, z.val ∈ omegaOneCenterAmbient (T : Subgroup G) ∧
      ∃ l ∈ L, MulAut.conj l v.val = z.val := by
  by_cases hf : v.val ∈ centralizer (L : Set G)
  · refine ⟨v,?_,1,one_mem _,by simp⟩
    apply (CoreMarking.mem_omega_iff (D := D) v).mpr
    intro t ht
    exact (normalizer_component_le_fixed_centralizer_at h structural D m
      (D.sylow_normalizes_component ht) v.val ⟨v.property,hf⟩).symm
  · obtain ⟨z,hz,_,hw⟩ := omega_representative_of_nonfixed D m
      (normalizer_component_le_module_at h structural D m) v hf
    exact ⟨z,hz,m.exists_conjugator_of_weight_eq v z hw.symm⟩

/-- Transport Burnside fusion from omega representatives back to the original core. -/
theorem core_normalizer_fusion_of_sylow_normalizer_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (v : V) (w : G) (hw : w ∈ V) (hc : IsConj v.val w) :
    ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w := by
  obtain ⟨x,hx,a,ha,hea⟩ := omega_conjugate_at h structural D m v
  obtain ⟨y,hy,b,hb,heb⟩ := omega_conjugate_at h structural D m ⟨w,hw⟩
  have hcxy : IsConj x.val y.val :=
    (isConj_iff.mpr ⟨a,hea⟩).symm.trans (hc.trans (isConj_iff.mpr ⟨b,heb⟩))
  obtain ⟨n,hn,hen⟩ := T.weakly_closed_normalizer_controls_centralizer_fusion
    (T : Subgroup G) le_rfl (fun g hg => mem_normalizer_iff_map_conj_eq.mpr
      (eq_of_le_of_card_ge hg (by rw [card_map_of_injective (MulAut.conj g).injective])))
    ((mem_omegaOneCenterAmbient_iff _ _).mp hx).2.2
    ((mem_omegaOneCenterAmbient_iff _ _).mp hy).2.2 hcxy
  refine ⟨b⁻¹*n*a,(normalizer (V : Set G)).mul_mem
    ((normalizer (V : Set G)).mul_mem
      ((normalizer (V : Set G)).inv_mem (D.normalizes hb))
      (normalizer_component_le_module_at h structural D m (hNT hn))) (D.normalizes ha),?_⟩
  change (b⁻¹*n*a)*v.val*(b⁻¹*n*a)⁻¹=w
  change a*v.val*a⁻¹=x.val at hea
  change b*w*b⁻¹=y.val at heb
  calc
    (b⁻¹*n*a)*v.val*(b⁻¹*n*a)⁻¹ = b⁻¹*(n*(a*v.val*a⁻¹)*n⁻¹)*b := by group
    _ = b⁻¹*y.val*b := by rw [hea,hen]
    _ = w := by rw [←heb]; group

/-- In the ordinary six-letter row the full module normalizer controls
ambient fusion, with no extra fusion or Sylow-normalizer premise. -/
theorem ordinary_core_normalizer_fusion_at
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (earlier : Theorem12213At KnownSimple.IsKnownSimple T)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (v : V) (w : G) (hw : w ∈ V) (hc : IsConj v.val w) :
    ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w :=
  core_normalizer_fusion_of_sylow_normalizer_at h structural D m
    (ordinary_sylow_normalizer_at hl h₀ h structural D m earlier eL) v w hw hc

/-- The original nonzero fixed part supplies its own applicability and marking,
and hence the actual Sylow-normalizer and full-module fusion clauses. -/
theorem ordinary_fixed_module_fusion_at
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (earlier : Theorem12213At KnownSimple.IsKnownSimple T)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) ∧
      ∀ (v : V) (w : G), w ∈ V → IsConj v.val w →
        ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w := by
  have hstar := Section03.Noncentrality.source1332_faithful_maximal
    h₀.qtke T h1332 h₀.local_component
  have h : Hypothesis1223 KnownSimple.IsKnownSimple T L :=
    h₀.hypothesis1311.hypothesis1223
      ⟨hstar,(Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T L).mp
        h₀.local_component |>.2⟩ (component_quotient_quasisimple h1332 h₀.local_component)
  obtain ⟨a⟩ := fixed h₀ L h₀.local_component V D hfixed
  obtain ⟨m⟩ := coreMarking_of_faithful_core_action D h.quasisimple a
  have hNT := ordinary_sylow_normalizer_at hl h₀ h structural D m earlier eL
  exact ⟨hNT,core_normalizer_fusion_of_sylow_normalizer_at h structural D m hNT⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
