module
public import Theory.Representation.BinaryOffender.ComponentSeedNormality
public import CFSG.Quasithin.Chapter13.Section07.ComponentPlaneSource
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.OrbitSource

/-!
# Normality of the component in the original plus-section construction

The original L₁ has no quotient of order two, so it normalizes a component
with at most two conjugates. Its action on the original seed V₃/(V₃∩U₀)
is nontrivial because [V₃,L₁]=V₃ and V₃∩U₀=V₁. The binary seed theorem
therefore makes the original T image normalize the selected component image.
Normalizer lifting and the Sylow index condition rule out an orbit of size two.

The final applications retain the original conjugator, quotient map, section
coordinates, minimal offender and whole moved module. The Irr⁺ and actor
conclusions are supplied by the completed original clauses (1–2); normality
is derived here and is never an input. The earlier 13.7.4 kernel equality
remains the same explicit source premise as in the selected-component producer.
Source: Aschbacher–Smith 13.7.15(3), printed pp.943–944.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion ChapterF.Section09.Setup ChapterB.QuasisimpleSource
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.TransvectionQuotients.FiveSeed.BarMarking
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

/-- The literal seed action normalizes the selected component, before choosing
a conjugator or using the actor catalogue. -/
theorem source_component_normal_of_seed
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hne : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) (H ⧸ pCore 2 H) W)
    (s : BinaryConjugationSection H (Section08.Source.UH H V₃)
      ((Section08.Source.UH H V₃) ⊓ centralizer (H.pCoreIn 2 : Set G))
      (σ.comp (QuotientGroup.mk' (pCore 2 H))))
    (hf : Function.Injective σ)
    {B : Subgroup (H ⧸ pCore 2 H)} (hB : IsMinimalBestOffender σ B)
    {K : Subgroup H} (hK : K.IsCComponent)
    (hKs : IsComponent (H ⧸ pCore 2 H) (K.map (QuotientGroup.mk' (pCore 2 H))))
    (hi : IsIrrPlus σ (K.map (QuotientGroup.mk' (pCore 2 H)))
      (subspaceCommutator σ ⊤ (K.map (QuotientGroup.mk' (pCore 2 H)))))
    (hc : ⁅K.map (QuotientGroup.mk' (pCore 2 H)),B⁆ = K.map (QuotientGroup.mk' (pCore 2 H)))
    (hd : Module.finrank (ZMod 2) (s.imageSpace V₃) = 2)
    (hm : subspaceCommutator σ ⊤ B ≤ s.imageSpace V₃) : K.Normal := by
  rcases Chapter1.Section02.component_normal_or_index_two_source (source_plus_local_sqtk d h) hK
    with hn | horbit
  · exact hn
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let U := Section08.Source.UH H V₃
  let U₀ := U ⊓ centralizer (H.pCoreIn 2 : Set G)
  let π := QuotientGroup.mk' (pCore 2 H)
  let J := (F.L₁.subgroupOf H).map π
  let S := ((T : Subgroup G).subgroupOf H).map π
  let P := s.imageSpace V₃
  let : Finite W := Finite.of_surjective (fun x : U => (s.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  let : FiniteDimensional (ZMod 2) W := Module.Finite.of_finite
  have hHG : H ≤ G₁ := by
    rw [d.first_normalizer]
    exact h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)
  have hL₁H : F.L₁ ≤ H := le_sup_left.trans h.local_le
  have hres : F.L₁ = sourceOne L T V₁ := by
    have hh := normalizer_residual_eq L V₁ (T : Subgroup G) T.isPGroup' d.normalizes_L
    change sourceOne L T V₁ =
      (pResidual 2 (L ⊓ normalizer (V₁ : Set G) : Subgroup G)).map
        (L ⊓ normalizer (V₁ : Set G)).subtype at hh
    have hn : normalizer (V₁ : Set G) = centralizer (V₁ : Set G) := h.normalizer_point_eq
    rw [hn] at hh
    exact hh.symm
  have hgen : ⁅V₃,F.L₁⁆ = V₃ := by
    rw [hres]
    exact ModelExclusions.seed_commutator_point_residual d
  have hpL : IsPPerfect 2 F.L₁ := isPPerfect_embedded_pResidual 2 _
  have hpLH : IsPPerfect 2 (F.L₁.subgroupOf H) := hpL.of_surjective
    (subgroupOfEquivOfLe hL₁H).symm.toMonoidHom (subgroupOfEquivOfLe hL₁H).symm.surjective
  have hpJ : IsPPerfect 2 J := hpLH.of_surjective
    (π.subgroupMap (F.L₁.subgroupOf H)) (π.subgroupMap_surjective _)
  have hseedU : V₃ ≤ U := le_conjugateSpanBy V₃ H
  have hseedN : F.L₁ ≤ normalizer (V₃ : Set G) := le_sup_left.trans h.local_normalizes
  have hP : J ≤ subspaceStabilizer σ P := by
    apply le_subspaceStabilizer
    rintro _ ⟨x,hx,rfl⟩ w hw
    obtain ⟨z,hz,rfl⟩ := (s.mem_imageSpace_iff V₃ w).mp hw
    let z' : U := ⟨(x : G) * z * (x : G)⁻¹,
      (mem_normalizer_iff.mp (s.normalized x.property) z).mp z.property⟩
    exact (s.mem_imageSpace_iff V₃ _).mpr ⟨z',
      (mem_normalizer_iff.mp (hseedN hx) z).mp hz, s.equivariant x z⟩
  have hinter : U₀ ⊓ V₃ = V₁ := by
    have he := seed_centralizer_eq_line d h (seed_noncentral_on_local_core h hHG hne)
    change V₃ ⊓ centralizer (H.pCoreIn 2 : Set G) = V₁ at he
    rw [← he]
    ext z
    exact ⟨fun hz => ⟨hz.2,hz.1.2⟩,fun hz => ⟨⟨hseedU hz.1,hz.2⟩,hz.1⟩⟩
  have hn : ¬ P ≤ fixedSpace σ J := by
    intro hfixed
    have hcomm : ⁅F.L₁,V₃⁆ ≤ U₀ := by
      apply commutator_le.mpr
      intro x hx z hz
      let xH : H := ⟨x,hL₁H hx⟩
      let zU : U := ⟨z,hseedU hz⟩
      have hv := hfixed ((s.mem_imageSpace_iff V₃ _).mpr ⟨zU,hz,rfl⟩)
        ⟨π xH,mem_map_of_mem π hx⟩
      have hzero : ((σ.comp π) xH - 1) (s.coordinates zU).toAdd = 0 := sub_eq_zero.mpr hv
      have hm := (s.displacement_mem_imageSpace_iff ⊥ bot_le xH zU).mp
        (hzero ▸ (s.imageSpace ⊥).zero_mem)
      simpa only [bot_sup_eq] using hm
    have h3 : V₃ ≤ U₀ := by rw [commutator_comm, hgen] at hcomm; exact hcomm
    exact (not_le_of_gt h.point_lt) ((le_inf h3 le_rfl).trans_eq hinter)
  have hSP : S ≤ subspaceStabilizer σ P := by
    apply le_subspaceStabilizer
    rintro _ ⟨x,hx,rfl⟩ w hw
    obtain ⟨z,hz,rfl⟩ := (s.mem_imageSpace_iff V₃ w).mp hw
    let z' : U := ⟨(x : G) * z * (x : G)⁻¹,
      (mem_normalizer_iff.mp (s.normalized x.property) z).mp z.property⟩
    exact (s.mem_imageSpace_iff V₃ _).mpr ⟨z',
      (mem_normalizer_iff.mp (d.seed_stable hx) z).mp hz, s.equivariant x z⟩
  let N := normalizer (K : Set H)
  let : N.Normal := normal_of_index_eq_two horbit
  have hq : IsPGroup 2 (H ⧸ N) := IsPGroup.of_card (n := 1) (by
    change N.index = 2^1
    simpa using horbit)
  have hLN : F.L₁.subgroupOf H ≤ N := by
    intro x hx
    have he := hpLH.hom_eq_one_of_isPGroup hq
      ((QuotientGroup.mk' N).comp (F.L₁.subgroupOf H).subtype)
    exact (QuotientGroup.eq_one_iff x).mp (DFunLike.congr_fun he ⟨x,hx⟩)
  have hJK : J ≤ normalizer (K.map π : Set (H ⧸ pCore 2 H)) :=
    (map_mono hLN).trans (K.le_normalizer_map π)
  have hSN := component_normalized_of_minimal_seed_plane σ hf hKs hi hB hc hpJ hJK
    P hP hd hn hm hSP
  let := pCore_isNilpotent (p := 2) (G := H)
  have hTN : (T : Subgroup G).subgroupOf H ≤ N := by
    change (T : Subgroup G).subgroupOf H ≤ normalizer (K : Set H)
    rw [← normalizer_cComponent_quotient hK (pCore 2 H)]
    exact map_le_iff_le_comap.mp hSN
  have hdiv := index_dvd_of_le hTN
  change (normalizer (K : Set H)).index ∣ ((T : Subgroup G).subgroupOf H).index at hdiv
  rw [horbit] at hdiv
  exact ((T.subtype h.T_le_H).not_dvd_index hdiv).elim

/-- Original13.7.15(3) for the selected component and actual plus coordinates. -/
theorem source_plus_component_normal
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hne : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (g : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hs : (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) g)^2 = 1)
    (hout : ¬ conjugate V₁ (g : G) ≤ Section08.Source.UH H V₃)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) (H ⧸ pCore 2 H) W)
    (s : Representation.BinaryConjugationSection H (Section08.Source.UH H V₃)
      ((Section08.Source.UH H V₃) ⊓ centralizer (H.pCoreIn 2 : Set G))
      (σ.comp (QuotientGroup.mk' (pCore 2 H))))
    (B : Subgroup (H ⧸ pCore 2 H)) (hB : IsMinimalBestOffender σ B)
    (hBA : B ≤ ((conjugate (Section08.Source.VH H V) (g : G) ⊓
      (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2).subgroupOf H).map
        (QuotientGroup.mk' (pCore 2 H)))
    (K : Subgroup H) (hKC : K.IsCComponent) (hK : IsComponent (H ⧸ pCore 2 H)
      (K.map (QuotientGroup.mk' (pCore 2 H))))
    (hk : PlusAction.kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H) = H.pCoreIn 2)
    (hcomm : ⁅K.map (QuotientGroup.mk' (pCore 2 H)),B⁆ = K.map (QuotientGroup.mk' (pCore 2 H))) : K.Normal := by
  have hp := source_plus_seed_plane d h hU hV hne g hs hout σ s B hBA
  have hi := (source_plus_component_irrPlus_and_actor d h hU hV hne g hs hout
    σ s B hB hBA K hK hk hcomm).1
  exact source_component_normal_of_seed d h hne σ s
    (source_plus_faithful_of_kernel_eq σ s hk) hB hKC hK hi hcomm hp.1 hp.2

/-- Construct all marked objects in13.7.15(1–3), including H-normality. -/
theorem exists_source_normal_component_irrPlus_and_actor
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hne : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (hk : PlusAction.kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H) = H.pCoreIn 2) :
    ∃ g : L,
      (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))
        (inclusion le_sup_left g))^2 = 1 ∧
      V ≤ V₃ ⊔ conjugate V₁ (g : G) ∧
      ¬ conjugate V₁ (g : G) ≤ Section08.Source.UH H V₃ ∧
      let U := Section08.Source.UH H V₃
      let U₀ := U ⊓ centralizer (H.pCoreIn 2 : Set G)
      let Q := (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2
      let A := conjugate (Section08.Source.VH H V) (g : G) ⊓ Q
      let π := QuotientGroup.mk' (pCore 2 H)
      ∃ hE : IsElementaryAbelian 2 U, letI := hE;
        ∃ (σ : Representation (ZMod 2) (H ⧸ pCore 2 H) (Additive (U ⧸ U₀.subgroupOf U)))
          (s : Representation.BinaryConjugationSection H U U₀ (σ.comp π))
          (B : Subgroup (H ⧸ pCore 2 H)) (K : Subgroup H),
          Function.Injective σ ∧ IsMinimalBestOffender σ B ∧
          B ≤ (A.subgroupOf H).map π ∧
          B ≤ centralizer (fittingSubgroup (H ⧸ pCore 2 H) : Set (H ⧸ pCore 2 H)) ∧
          K.IsCComponent ∧ IsComponent (H ⧸ pCore 2 H) (K.map π) ∧
          B ≤ normalizer (K.map π : Set (H ⧸ pCore 2 H)) ∧
          ⁅K.map π,B⁆ = K.map π ∧
          Module.finrank (ZMod 2) (s.imageSpace V₃) = 2 ∧
          subspaceCommutator σ ⊤ B ≤ s.imageSpace V₃ ∧
          IsIrrPlus σ (K.map π) (subspaceCommutator σ ⊤ (K.map π)) ∧
          SmallMoved.ActorList (K.map π) ∧ K.Normal := by
  obtain ⟨g,hs,hspan,hout,hE,σ,s,B,K,hf,hB,hBA,hc,hK,hKs,hn,hcomm,hd,hm,hi,ha⟩ :=
    exists_source_component_irrPlus_and_actor d h hU hV hne hk
  let := hE
  have hnormal := source_component_normal_of_seed d h hne σ s hf hB hK hKs hi hcomm hd hm
  exact ⟨g,hs,hspan,hout,hE,σ,s,B,K,hf,hB,hBA,hc,hK,hKs,hn,hcomm,hd,hm,hi,ha,hnormal⟩

end CFSG.Quasithin.Chapter13.Section07
