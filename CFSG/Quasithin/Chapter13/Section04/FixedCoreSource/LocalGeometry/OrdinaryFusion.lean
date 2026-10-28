module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.OmegaIndex
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NormalizerResidual
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.AugmentationAlternative
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockCentralizerAlternatingComplete
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.MovedSectionModel
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.FirstFlagNormalizer
public import Theory.GroupTheory.WeakClosureSetFusion

/-!
# Ordinary fixed-core normalizer fusion

The full omega-centralizer has the same embedded prime-to-three residual
as the original point centralizer in L. Hence the Sylow normalizer fixes
that residual and its parabolic two-core. The augmentation Baumann/short
alternative gives containment in N_G(L); in the short branch the original
core coordinates construct the actual alternating-six block model.

Every vector has an L-conjugate in the Sylow omega-center. Burnside fusion
there, transported through those L-conjugators, gives N_G(V)-control of
ambient fusion in the whole five-dimensional module. The ordinary quotient,
earlier structural results and natural large-distance theorem remain explicit.
OrdinaryFusionAssembly applies this at the original and reciprocal cores.

Source: Aschbacher--Smith 13.2.2(5),(7), 13.4.2(3) and 13.4.3,
printed pp.877--878,897; A.1.35, printed p.30.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation BinaryPermutation
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Solvable
open Section08.TransvectionRecognition.Component.ModelExtension
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Identify the literal full omega-centralizer residual with the original first residual. -/
theorem ordinary_omega_residual
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (earlier : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G)) :
    (primeToResidual 3 (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))).map
      (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)).subtype =
      firstCentralizerResidual L z.val := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let C := centralizer (Z : Set G)
  have hCM : C ≤ normalizer (L : Set G) := by
    rw [←fixed_generator_centralizer h structural D m
      ⟨m.constant.property,m.constant_fixed⟩
      (fun he => m.constant_ne_one (Subtype.ext he))]
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (hx m.constant.val (m.constant_mem_central_four h structural).2).symm
  have hLC : L ⊓ C = L ⊓ centralizer ({z.val} : Set G) := by
    apply le_antisymm (inf_le_inf_left L (centralizer_le (Set.singleton_subset_iff.mpr hz)))
    rintro l ⟨hl,hzl⟩
    refine ⟨hl,?_⟩
    have hV : V ⊓ Z ≤ centralizer ({l} : Set G) := by
      rw [first_fixed_plane_eq h structural D m z hz hzL]
      apply sup_le
      · intro v hv
        exact mem_centralizer_singleton_iff.mpr (hv.2 l hl).symm
      · exact zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
          (mem_centralizer_singleton_iff.mp hzl).symm)
    have hs : Z = (V ⊓ Z) ⊔ (Z ⊓ centralizer (L : Set G)) :=
      original_omega_decomposition h₀ h structural D m earlier
    have hZ : Z ≤ centralizer ({l} : Set G) := by
      rw [hs]
      exact sup_le hV (fun x hx => mem_centralizer_singleton_iff.mpr (hx.2 l hl).symm)
    exact fun x hx => mem_centralizer_singleton_iff.mp (hZ hx)
  have he := embedded_primeToResidual_intersection_of_le 3 (normalizer (L : Set G)) L C hCM
    (normalizer_primeToThree_residual h structural eL)
  rw [hLC] at he
  simpa only [firstCentralizerResidual_eq] using he

omit [Finite G] in
/-- The actual natural quotient of the chosen core identifies the intrinsic short-block model. -/
theorem alternating_block_of_short_core
    (D : ChosenModule T L V) (m : CoreMarking D) (hb : ChapterC.IsShort L) :
    ChapterC.IsAlternatingBlock L 6 := by
  let e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6) :=
    (QuotientGroup.quotientMulEquivOfEq
      (centralCore_eq_twoCore_of_short_core_marking D m hb).symm).trans m.quotient
  let f : V →* Multiplicative (natural (Fin 6)) :=
    ((coreToNatural (Fin 6)).toAddMonoidHom.toMultiplicative).comp m.coordinate.toMonoidHom
  have hf : Function.Surjective f := by
    intro w
    obtain ⟨v,hv⟩ := coreToNatural_surjective w.toAdd
    obtain ⟨u,hu⟩ := m.coordinate.surjective (Multiplicative.ofAdd v)
    refine ⟨u,?_⟩
    change Multiplicative.ofAdd (coreToNatural (Fin 6) (m.coordinate u).toAdd) = w
    rw [hu]
    exact congrArg Multiplicative.ofAdd hv
  have hk : f.ker = (V ⊓ centralizer (L : Set G)).subgroupOf V := by
    ext v
    rw [MonoidHom.mem_ker]
    change coreToNatural (Fin 6) (m.coordinate v).toAdd = 0 ↔ _
    have hkzero : coreToNatural (Fin 6) (m.coordinate v).toAdd = 0 ↔
        (m.coordinate v).toAdd.val ∈ constants (Fin 6) := by
      rw [←Subtype.val_inj]
      exact Submodule.Quotient.mk_eq_zero _
    rw [hkzero]
    exact (m.mem_fixed_iff v).symm.trans (by simp only [mem_subgroupOf,mem_inf,v.property,true_and])
  let c : BinaryConjugationSection L V (V ⊓ centralizer (L : Set G))
      ((alternatingNaturalRepresentation (Fin 6)).comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))) := {
    section_le := D.le_component
    kernel_le := inf_le_left
    normalized := D.normalizes
    coordinates := f
    onto := hf
    kernel_eq := hk
    equivariant := by
      intro l v
      change coreToNatural (Fin 6) (m.coordinate
        (V.normalizerMonoidHom ⟨l.val,D.normalizes l.property⟩ v)).toAdd = _
      rw [m.equivariant]
      exact coreToNatural_equivariant _ _ }
  have hc : BinaryConjugationSection L ⁅V,L⁆ (⁅V,L⁆ ⊓ centralizer (L : Set G))
      ((alternatingNaturalRepresentation (Fin 6)).comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))) := by
    rw [←D.eq_commutator]
    exact c
  refine ⟨by decide,hb,(naturalMulAction (Fin 6)).comp (alternatingGroup (Fin 6)).subtype,
    ⟨ChapterC.blockModelOfIdentifiedMovedSection L V
      ((chosen_eq_block_layer D hb).trans D.eq_commutator) e
      (alternatingNaturalRepresentation (Fin 6))
      ((naturalMulAction (Fin 6)).comp (alternatingGroup (Fin 6)).subtype)
      (fun _ _ => rfl) hc⟩,fun _ _ => rfl⟩

/-- Apply the completed alternating-block normalizer theorem to this actual model. -/
theorem sylow_normalizer_le_of_short_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (m : CoreMarking D) (hb : ChapterC.IsShort L) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) :=
  RecognitionSource.FusionReducibleNormalizer.sylow_normalizer_le_of_alternating_block
    h D m.fixed_ne_bot (alternating_block_of_short_core D m hb)


/-- The original ordinary augmentation alternative controls the full Sylow normalizer. -/
theorem ordinary_sylow_normalizer
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (earlier : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨z,_,hz,hzL,_⟩ := exists_nonfixed_omega_escape h₀ h structural D m earlier
  have he := ordinary_omega_residual h₀ h structural D m earlier eL z hz hzL
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
  rcases Nonsolvable.ordinary_augmentation_baumann_alternative_of_largeDistance
      hl h structural D m eL z hz hzL with hbound | hb
  · exact (hnR.trans (normalizer_le_normalizer_baumann R)).trans hbound
  · exact sylow_normalizer_le_of_short_core h D m hb

private theorem omega_conjugate
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D) (v : V) :
    ∃ z : V, z.val ∈ omegaOneCenterAmbient (T : Subgroup G) ∧
      ∃ l ∈ L, MulAut.conj l v.val = z.val := by
  by_cases hf : v.val ∈ centralizer (L : Set G)
  · refine ⟨v,?_,1,one_mem _,by simp⟩
    apply (CoreMarking.mem_omega_iff (D := D) v).mpr
    intro t ht
    exact (normalizer_component_le_fixed_centralizer h structural D m
      (D.sylow_normalizes_component ht) v.val ⟨v.property,hf⟩).symm
  · obtain ⟨z,hz,_,hw⟩ := omega_representative_of_nonfixed D m
      (normalizer_component_le_module h structural D m) v hf
    exact ⟨z,hz,m.exists_conjugator_of_weight_eq v z hw.symm⟩

/-- Transport Burnside fusion from omega representatives back to the original core. -/
theorem core_normalizer_fusion_of_sylow_normalizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (v : V) (w : G) (hw : w ∈ V) (hc : IsConj v.val w) :
    ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w := by
  obtain ⟨x,hx,a,ha,hea⟩ := omega_conjugate h structural D m v
  obtain ⟨y,hy,b,hb,heb⟩ := omega_conjugate h structural D m ⟨w,hw⟩
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
      (normalizer_component_le_module h structural D m (hNT hn))) (D.normalizes ha),?_⟩
  change (b⁻¹*n*a)*v.val*(b⁻¹*n*a)⁻¹=w
  change a*v.val*a⁻¹=x.val at hea
  change b*w*b⁻¹=y.val at heb
  calc
    (b⁻¹*n*a)*v.val*(b⁻¹*n*a)⁻¹ = b⁻¹*(n*(a*v.val*a⁻¹)*n⁻¹)*b := by group
    _ = b⁻¹*y.val*b := by rw [hea,hen]
    _ = w := by rw [←heb]; group


/-- In the ordinary six-letter row the full module normalizer controls
ambient fusion, with no extra fusion or Sylow-normalizer premise. -/
theorem ordinary_core_normalizer_fusion
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (earlier : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (v : V) (w : G) (hw : w ∈ V) (hc : IsConj v.val w) :
    ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w :=
  core_normalizer_fusion_of_sylow_normalizer h structural D m
    (ordinary_sylow_normalizer hl h₀ h structural D m earlier eL) v w hw hc

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
