module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.FixedSpaces.PrimeResidual
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.FixedSpaces.Source

/-!
# Outside intersections and uniform fixed spaces for every source row

The canonical residual O^{p′}(M∞), at an actual odd prime divisor of the
component quotient, supplies orbit rigidity and localization in L₀.
The original product quotient then identifies a component fixing a common
nonfixed point. The earlier bound N_G(L)≤M excludes its outside conjugator.

This proves the whole intersection obligation, including Suzuki, and feeds
the existing displacement and action-kernel arguments to obtain offender
normalization and uniform fixed spaces. GeometryAt retains only the earlier
HalfSylowUniqueAt source theorem, owned by qt-d-10-nona5-half-sylow-unique;
its unconditional assembly remains with qt-d-10-nona5-point-control. Model
bounds and final small-offender assembly remain with qt-d-10-nona5-small-offender.
Source: Aschbacher--Smith 10.2.6(2), 10.2.10 and 10.2.12, pp.749,753--754.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition.FixedSpaces
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- Outside intersections use same-component localization rather than solvability of all proper subgroups. -/
theorem fixed_factor_inf_conjugate_eq_bot
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (U : Subgroup G) (hUV : U ≤ D.fullModule)
    (hUL : U ≤ centralizer (L : Set G))
    (hcent : ∀ u ∈ U, u ≠ 1 → centralizer ({u} : Set G) ≤ D.maximalLocal)
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    {g : G} (hg : g ∉ D.maximalLocal) :
    U ⊓ U.map (MulAut.conj g).toMonoidHom = ⊥ := by
  apply eq_bot_iff.mpr
  rintro v ⟨hv,u,hu,rfl⟩
  by_cases hu1 : u = 1
  · simp [hu1]
  have hv1 : (MulAut.conj g) u ≠ 1 :=
    fun he => hu1 ((MulAut.conj g).map_eq_one_iff.mp he)
  let C := centralizer ({(MulAut.conj g) u} : Set G)
  have hCM : C ≤ D.maximalLocal := hcent _ hv hv1
  have hCMg : C ≤ D.maximalLocal.map (MulAut.conj g).toMonoidHom := by
    rw [show C = (centralizer ({u} : Set G)).map (MulAut.conj g).toMonoidHom from
      (CentralizerSmallKernelTransport.map_centralizer (MulAut.conj g) u).symm]
    exact map_mono (hcent u hu hu1)
  by_cases hvR : (MulAut.conj g) u ∈ centralizer (localOrbit T L : Set G)
  · exact (hg ((orbit_le_conjugate_maximal_iff D hn g).mp
      ((show localOrbit T L ≤ C from fun r hr =>
        mem_centralizer_singleton_iff.mpr (hvR r hr)).trans hCMg))).elim
  let A := L.map (MulAut.conj g).toMonoidHom
  have hAC : A ≤ C := by
    rintro x ⟨l,hl,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using congrArg (MulAut.conj g) (hUL hu l hl)
  have hAR : A ≤ localOrbit T L :=
    conjugate_component_le_orbit D hn g (hAC.trans hCM)
  have hAL : A ≤ L := isomorphic_component_point_le D hn (hUV hv) (hUL hv) hvR A
    ((MulAut.conj g).subgroupMap L).symm hAR hAC
  have he : A = L := eq_of_le_of_card_ge hAL
    (Nat.card_congr ((MulAut.conj g).subgroupMap L).toEquiv).le
  exact (hg (hNL (mem_normalizer_iff_map_conj_eq.mpr he))).elim

/-- The actual moved factor has trivial intersections outside M for every original component model. -/
theorem moved_inf_conjugate_eq_bot
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (t : G) (ht : t ∈ (T : Subgroup G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤
      centralizer (L : Set G))
    (hcent : ∀ u ∈ ⁅D.fullModule,L⁆, u ≠ 1 →
      centralizer ({u} : Set G) ≤ D.maximalLocal)
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    {g : G} (hg : g ∉ D.maximalLocal) :
    ⁅D.fullModule,L⁆ ⊓ (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom = ⊥ := by
  let M := D.maximalLocal
  let W := ⁅D.fullModule,L⁆
  let U := W.map (MulAut.conj t).toMonoidHom
  have htM : t ∈ M := (le_normalizer_componentOrbit L T) ht
  have hMM : M.map (MulAut.conj t).toMonoidHom = M :=
    mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer htM)
  have hWV : W ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
    (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule)
  have hUV : U ≤ D.fullModule := by
    have hmV : D.fullModule.map (MulAut.conj t).toMonoidHom = D.fullModule :=
      mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule htM)
    exact (map_mono hWV).trans_eq hmV
  have hcU : ∀ u ∈ U, u ≠ 1 → centralizer ({u} : Set G) ≤ M := by
    rintro u ⟨w,hw,rfl⟩ hne
    have hwne : w ≠ 1 := fun he => hne (by simp [he])
    change centralizer ({(MulAut.conj t) w} : Set G) ≤ M
    rw [←CentralizerSmallKernelTransport.map_centralizer (MulAut.conj t) w]
    exact (map_mono (hcent w hw hwne)).trans_eq hMM
  have hnot : t * g * t⁻¹ ∉ M := by
    intro hh
    apply hg
    simpa [mul_assoc] using M.mul_mem (M.mul_mem (M.inv_mem htM) hh) htM
  have hTI := fixed_factor_inf_conjugate_eq_bot D hn U hUV hcross hcU hNL hnot
  apply eq_bot_iff.mpr
  rintro x ⟨hx,w,hw,rfl⟩
  have hmem : (MulAut.conj t) ((MulAut.conj g) w) ∈
      U ⊓ U.map (MulAut.conj (t * g * t⁻¹)).toMonoidHom := by
    refine ⟨mem_map_of_mem _ hx, (MulAut.conj t) w, mem_map_of_mem _ hw, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  rw [hTI,mem_bot] at hmem
  exact (MulAut.conj t).map_eq_one_iff.mp hmem

/-- Both source intersection fields follow from the original normalizer bound,
with no prime-divisibility or model assumption. -/
theorem intersectionInputs_of_normalizer
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (c : Context D)
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal) : IntersectionInputs D := by
  obtain ⟨t,ht,htn⟩ := SetLike.not_le_iff_exists.mp c.nonnormal
  exact ⟨fun _ hx => moved_inf_conjugate_eq_bot D c.nonnormal t ht
    (c.crossed t ht htn) c.pointCentralizers hNL hx,
    fun x hx => (orbit_le_conjugate_maximal_iff D c.nonnormal x).mp hx⟩

/-- The complete published intersection obligation with its independent
10.2.6 normalizer premise. -/
theorem source_intersectionsOfNormalizersAt : IntersectionsOfNormalizersAt T :=
  fun _ D c hNL => Or.inr (intersectionInputs_of_normalizer D c hNL)

/-- The uniform fixed-space result uses the actual original offender. -/
theorem fixedSpaceGeometry_of_normalizer
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (c : Context D)
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal) : FixedSpaceGeometry D :=
  fixedSpaceGeometry_of_source_inputs D c (source_actionInputs D c)
    (intersectionInputs_of_normalizer D c hNL)

/-- Every large row is excluded once its literal local bounds and the earlier
component-normalizer control are supplied. -/
theorem large_module_false_of_normalizer
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) {g : G}
    (c : Configuration T D g) (b : LargeModuleBounds D)
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal) : False := by
  let ctx : Context D := ⟨c.many,c.minimal,c.nonnormal,c.notA5,c.pointCentralizers,
    b.crossed,b.fixed_size_gt_eight⟩
  exact b.false_of_configuration c (fixedSpaceGeometry_of_normalizer D ctx hNL)

/-- The complete original intersections contract, retaining only the earlier
independent half-Sylow premise. -/
theorem source_intersectionsAt_of_halfSylowUnique
    (hhalf : PointControl.HalfSylowUniqueAt T) : IntersectionsAt T :=
  intersectionsAt_of_halfSylowUnique hhalf source_intersectionsOfNormalizersAt

/-- GeometryAt has no remaining intersection or fixed-space callback.
The existing half-Sylow source owner supplies the sole earlier premise. -/
theorem geometryAt_of_halfSylowUnique
    (hhalf : PointControl.HalfSylowUniqueAt T) : GeometryAt T :=
  geometryAt_of_halfSylowUnique_and_intersections hhalf source_intersectionsOfNormalizersAt

/-- The original recognition consumer now needs only the source model bounds
and the independently owned half-Sylow theorem. -/
theorem recognition_of_models_and_halfSylowUnique
    (hmodels : ModelBoundsAt T) (hhalf : PointControl.HalfSylowUniqueAt T) : RecognitionAt T :=
  recognition_of_model_bounds_and_geometry hmodels (geometryAt_of_halfSylowUnique hhalf)

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition.FixedSpaces
