module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2SourceContainedPoint
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2SourceReciprocity
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2SourceInterchange

/-!
# The original reciprocal core in the nonoffender case

For the natural four-group marking constructed in G2SourceContainedPoint,
relative normality makes the image of D = U ∩ Qα invariant under the actual
point parabolic. Commutators contain the marked three-space, and their
common point displacement puts D inside the natural polar hyperplane.
The invariant-subspace calculation and the selected index comparison then
identify its image with that hyperplane.

The recognized natural/Weyl no-transvection bound puts the fixed preimage
inside D. Thus the kernel of the natural projection is already contained
in the image of D, and the literal quotient U/D has order two. Since Uα*
has order four, the actual 14.7.58 interchange rules out a nonoffender with
Zα ≤ V. In the offender case the constructed full marking and the separate
14.7.61 reciprocal symmetry exclude Zα from U. The final application
therefore excludes the critical point from the original seed V.

The nonoffender point-to-seed incidence argument of 14.7.60–61, and the
literal final four-cycle construction, remain obligations of this source
branch. No point marking, invariant hyperplane, index equality or symmetry
callback is assumed here. The earlier faithful action, generalized-Fitting,
structural, F.9.18 and core-commutator inputs retain their source producers
and final discharge by qt-d-14775-source.

Source: Aschbacher–Smith, 14.7.60–62, printed pp.1067–1068. The concrete
natural-module calculations retain the attribution in LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source
open Chapter12.Section08 CriticalFusion.Source
open Atlas.G2.Natural.BinaryPointFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  {σ : Representation (ZMod 2) (HStar F.H) W}
  (c : BinaryConjugationSection F.H F.U (F.Vi 1) (σ.comp (starMap F)))

private theorem critical_core_image_codimension
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hf : Function.Injective σ) (path : CriticalPath (L := L) F) :
    Module.finrank (ZMod 2) (W ⧸ c.imageSpace (F.U ⊓ path.Qα)) =
      Nat.log 2 ((F.U ⊓ path.Qα).relIndex F.U) := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  let : Finite W := Finite.of_surjective (fun x : F.U => (c.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  have hker : (σ.comp (starMap F)).ker = pCore 2 F.H := by
    rw [MonoidHom.ker_comp_of_injective (starMap F) σ hf]
    exact QuotientGroup.ker_mk' _
  have hPD : F.Vi 1 ≤ F.U ⊓ path.Qα := le_inf c.kernel_le
    (LocalReduction.point_le_reciprocal_core_of_kernel h structural hker c path)
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 F.U).to_quotient
    ((F.U ⊓ path.Qα).subgroupOf F.U) |>.exists_card_eq
  have hindex : (F.U ⊓ path.Qα).relIndex F.U = 2^n := hn
  have hd := c.imageSpace_codimension_of_index _ inf_le_left hPD n hindex
  have hq := (c.imageSpace (F.U ⊓ path.Qα)).finrank_quotient_add_finrank
  rw [hindex,Nat.log_pow Nat.one_lt_two]
  omega

omit [Finite G] in
include c in
private theorem source_core_image_stable
    (path : CriticalPath (L := L) F) :
    ∀ a ∈ star F (F.H ⊓ centralizer (path.Zα : Set G)),
      ∀ v ∈ c.imageSpace (F.U ⊓ path.Qα),
        σ a v ∈ c.imageSpace (F.U ⊓ path.Qα) := by
  have hn : F.H ⊓ centralizer (path.Zα : Set G) ≤
      normalizer (F.U ⊓ path.Qα : Set G) := by
    apply (le_inf (inf_le_left.trans c.normalized) _).trans inf_normalizer_le_normalizer_inf
    rw [partner_centralizer path]
    exact inf_le_right.trans ((conjugate F.H path.conjugator).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 (conjugate F.H path.conjugator))))
  rintro _ ⟨a,ha,rfl⟩ v hv
  obtain ⟨x,hx,rfl⟩ := (c.mem_imageSpace_iff _ _).mp hv
  refine (c.mem_imageSpace_iff _ _).mpr ⟨⟨a*x*(a:G)⁻¹,
    (mem_normalizer_iff.mp (c.normalized a.property) x).mp x.property⟩,
    (mem_normalizer_iff.mp (hn (show (a : G) ∈ _ from ha)) (x : G)).mp hx,c.equivariant a x⟩

include c in
private theorem source_commutator_le_reciprocal_core
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U) (hf : Function.Injective σ)
    (path : CriticalPath (L := L) F) (hAH : path.Uα ≤ F.H) :
    ⁅F.U,path.Uα⁆ ≤ F.U ⊓ path.Qα := by
  let := hab
  have hUQ : F.U ≤ F.H.pCoreIn 2 := (le_centralizer _).trans (source_centralizer_U_le_core c hf)
  have hAQ : path.Uα ≤ path.Qα := by
    have hh := map_mono (f := (MulAut.conj path.conjugator⁻¹).toMonoidHom) hUQ
    rw [map_pCoreIn_of_injective 2 _ _ (MulAut.conj path.conjugator⁻¹).injective] at hh
    exact hh
  refine le_inf (le_normalizer_iff_commutator_le_left.mp (hAH.trans c.normalized)) ?_
  rw [commutator_comm]
  exact (commutator_mono hAQ le_rfl).trans
    (le_normalizer_iff_commutator_le_left.mp ((reciprocal_placement h path).trans
      ((conjugate F.H path.conjugator).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 (conjugate F.H path.conjugator))))))

omit [Finite G] in
include c in
private theorem source_point_coordinate_image
    (path : CriticalPath (L := L) F)
    (r : W →ₗ[ZMod 2] (Fin 6 → ZMod 2))
    (t : F.U) (ht : (t : G) ∈ path.Zα)
    (hrt : r (c.coordinates t).toAdd = Pi.single 0 1) :
    (c.imageSpace path.Zα).map r = Atlas.G2.Natural.BinaryPointFlag.pointLine := by
  have ht1 : (t : G) ≠ 1 := by
    intro hh
    have ht' : t = 1 := Subtype.ext hh
    have hz := congrFun hrt 0
    simp [ht'] at hz
  have hcard : Nat.card path.Zα = 2 := by
    rw [CriticalPath.Zα,conjugate,card_map_of_injective (MulAut.conj path.conjugator⁻¹).injective]
    simpa using F.card 1 (by decide)
  have hgen := zpowers_eq_top_of_prime_card hcard
    (g := (⟨t,ht⟩ : path.Zα)) (fun hh => ht1 (congrArg Subtype.val hh))
  have hZ : path.Zα = zpowers (t : G) := by
    have hh := congrArg (Subgroup.map path.Zα.subtype) hgen
    rw [MonoidHom.map_zpowers,←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh.symm
  rw [hZ,imageSpace_zpowers c t,Submodule.map_span,Set.image_singleton,hrt]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ rfl
    apply Atlas.G2.Natural.BinaryPointFlag.mem_pointLine _ |>.mpr
    intro j hj
    simp [hj]
  · intro v hv
    have hv' := (Atlas.G2.Natural.BinaryPointFlag.mem_pointLine v).mp hv
    have he : v = v 0 • Pi.single 0 1 := by
      ext j
      by_cases hj : j = 0
      · subst j; simp
      · simp [hj,hv' j hj]
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))


private theorem nonoffender_core_hyperplane_of_marking
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hf : Function.Injective σ)
    (path : CriticalPath (L := L) F) (hplace : path.Uα ≤ F.Ri L 1)
    (selection : path.RankSelection) (hn : ¬ IsOffender σ (star F path.Uα))
    (f : HStar F.H →* Atlas.G2.Model (ZMod 2))
    (hJ : commutator (Atlas.G2.Model (ZMod 2)) ≤ f.range)
    (q : W →ₗ[ZMod 2] Atlas.G2.Natural.Space (ZMod 2)) (hq : Function.Surjective q)
    (he : ∀ a v, q (σ a v) = Atlas.G2.Natural.action (ZMod 2) (f a) (q v))
    (hfix : ∀ a v, σ a v = v ↔
      Atlas.G2.Natural.action (ZMod 2) (f a) (q v) = q v)
    (hC : (star F (F.H ⊓ centralizer (path.Zα : Set G))).map f =
      Atlas.G2.BinaryCore.secondParabolic ⊓ f.range)
    (hA : (star F path.Uα).map f = Atlas.G2.BinaryCore.natural)
    (t : F.U) (ht : (t : G) ∈ path.Zα)
    (hqt : Atlas.G2.Restricted.NaturalCoordinates.equiv (ZMod 2)
      (q (c.coordinates t).toAdd) = Pi.single 0 1) :
    (c.imageSpace (F.U ⊓ path.Qα)).map
      ((Atlas.G2.Restricted.NaturalCoordinates.equiv (ZMod 2)).toLinearMap.comp q) =
      Atlas.G2.Natural.BinaryPointFlag.hyperplane := by
  let : Finite W := Finite.of_surjective (fun x : F.U => (c.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  let E := Atlas.G2.Restricted.NaturalCoordinates.equiv (ZMod 2)
  let r := E.toLinearMap.comp q
  let τ := Atlas.G2.Restricted.NaturalCoordinates.action (ZMod 2)
  let D := F.U ⊓ path.Qα
  let S := (c.imageSpace D).map r
  have hr : Function.Surjective r := E.surjective.comp hq
  have her (a) (v) : r (σ a v) = τ (f a) (r v) := by
    change E (q (σ a v)) = _
    rw [he]
    exact LinearMap.congr_fun
      ((Atlas.G2.Restricted.NaturalCoordinates.repEquiv (ZMod 2)).isIntertwining' (f a)) (q v)
  have hfixr (a) (v) : σ a v = v ↔ τ (f a) (r v) = r v := by
    rw [←her]
    change _ ↔ E (q (σ a v)) = E (q v)
    rw [E.injective.eq_iff,he]
    exact hfix a v
  have hAH : path.Uα ≤ F.H := hplace.trans
    ((pCoreIn_le 2 (F.Li L 1 ⊔ (T : Subgroup G))).trans
      (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)))
  have hcomm := source_commutator_le_reciprocal_core c h hab hf path hAH
  have hmoved : subspaceCommutator τ ⊤ Atlas.G2.BinaryCore.natural ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a,ha,v,_,rfl⟩
    rw [←hA] at ha
    obtain ⟨a,ha,rfl⟩ := ha
    obtain ⟨a,ha,rfl⟩ := ha
    obtain ⟨w,rfl⟩ := hr v
    refine ⟨σ (starMap F a) w-w,?_,?_⟩
    · apply c.displacement_range_le_imageSpace_of_commutator_le path.Uα D
        (by rwa [commutator_comm]) a ha
      exact ⟨w,rfl⟩
    · rw [map_sub,her]
  have hseed : Atlas.G2.Natural.BinaryPointFlag.seed ≤ S := by
    let : IsElementaryAbelian 2 Atlas.G2.BinaryCore.natural :=
      IsElementaryAbelian.of_injective (inclusion Atlas.G2.BinaryCore.natural_le_elementary)
        (inclusion_injective _)
    have hne : Atlas.G2.BinaryCore.natural ≠ ⊥ := by
      intro hh
      have hc := Atlas.G2.BinaryCore.card_natural
      rw [hh,card_bot] at hc
      omega
    have hh := Atlas.G2.Natural.BinaryPointFlag.normal_elementary_displacement_eq_seed
      Atlas.G2.BinaryCore.natural
      (Atlas.G2.BinaryCore.natural_le_elementary.trans
        (Atlas.G2.BinaryCore.elementary_le_core.trans Atlas.G2.BinaryCore.core_le_unipotent))
      (inf_le_left.trans Atlas.G2.BinaryCore.secondParabolic_normalizes_natural) hne
    exact hh ▸ hmoved
  have hstable : ∀ a ∈ Atlas.G2.BinaryParabolicPair.derivedSecondAmbient,
      ∀ v ∈ S, τ a v ∈ S := by
    intro a ha v hv
    have haC : a ∈ (star F (F.H ⊓ centralizer (path.Zα : Set G))).map f := by
      rw [hC]
      exact ⟨ha.1,hJ ha.2⟩
    obtain ⟨b,hb,rfl⟩ := haC
    obtain ⟨v,hv,rfl⟩ := hv
    exact ⟨σ b v,source_core_image_stable c path b hb v hv,her b v⟩
  have hpoint := source_point_coordinate_image c path r t ht hqt
  have hDpre : D ≤ commutatorPreimage F.U path.Uα path.Zα :=
    le_commutatorPreimage inf_le_left
      ((commutator_mono inf_le_right le_rfl).trans (reciprocal_core_commutator c path))
  have hdisp := (critical_linear_bounds c h path hplace selection).2.2
  have hShyper : S ≤ Atlas.G2.Natural.BinaryPointFlag.hyperplane := by
    rintro _ ⟨v,hv,rfl⟩
    have ha : Atlas.G2.rootA (1 : ZMod 2) ∈ (star F path.Uα).map f := by
      rw [hA]
      exact Atlas.G2.BinaryCore.z_mem_natural
    obtain ⟨a,ha,hea⟩ := ha
    have hd : τ (Atlas.G2.rootA 1) (r v)-r v ∈
        Atlas.G2.Natural.BinaryPointFlag.pointLine := by
      rw [←hpoint]
      refine ⟨σ a v-v,hdisp a ha v (c.imageSpace_mono hDpre hv),?_⟩
      rw [map_sub,her,hea]
    have hd1 := (Atlas.G2.Natural.BinaryPointFlag.mem_pointLine _).mp hd 1 (by decide)
    apply Atlas.G2.Natural.BinaryPointFlag.mem_hyperplane _ |>.mpr
    simpa [τ] using hd1
  have hnotseed : S ≠ Atlas.G2.Natural.BinaryPointFlag.seed := by
    intro hs
    have hDF : c.imageSpace D ≤ fixedSpace σ (star F path.Uα) := by
      intro v hv a
      apply (hfixr a v).mpr
      apply Atlas.G2.Natural.BinaryPointFlag.elementary_fixes_seed
      · apply Atlas.G2.BinaryCore.natural_le_elementary
        exact hA ▸ mem_map_of_mem f a.property
      · rw [←hs]
        exact Submodule.mem_map_of_mem hv
    have hd := critical_core_image_codimension c h hab structural hf path
    have hs := selection.comparison
    have hdim := Submodule.finrank_mono hDF
    have hq := (c.imageSpace D).finrank_quotient_add_finrank
    have hsum := fixedCodim_add_finrank σ (star F path.Uα)
    apply hn
    refine ⟨critical_elementary h hab path hplace selection,?_⟩
    change _ ≤ Nat.log 2 (Nat.card (star F path.Uα))
    change Module.finrank (ZMod 2) (W ⧸ c.imageSpace D) = _ at hd
    omega
  rcases Atlas.G2.Natural.BinaryPointFlag.point_invariant_interval S hseed hstable with hs|hs|hs
  · exact (hnotseed hs).elim
  · exact hs
  · have h5 := hShyper (hs ▸ (Submodule.mem_top : (Pi.single 5 1 : Fin 6 → ZMod 2) ∈ ⊤))
    have hz : (1 : ZMod 2) = 0 := by
      simpa using (Atlas.G2.Natural.BinaryPointFlag.mem_hyperplane _).mp h5
    exact (one_ne_zero hz).elim


private theorem hyperplane_image_codimension {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (S : Submodule (ZMod 2) M) (r : M →ₗ[ZMod 2] (Fin 6 → ZMod 2))
    (hr : Function.Surjective r) (hk : r.ker ≤ S)
    (hs : S.map r = Atlas.G2.Natural.BinaryPointFlag.hyperplane) :
    Module.finrank (ZMod 2) (M ⧸ S) = 1 := by
  let j := S.mapQ (S.map r) r (Submodule.le_comap_map r S)
  have hi : Function.Injective j := by
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.ker_mapQ,Submodule.comap_map_eq,sup_eq_left.mpr hk,Submodule.mkQ_map_self]
  have hj : Function.Surjective j := by
    intro v
    obtain ⟨w,rfl⟩ := (S.map r).mkQ_surjective v
    obtain ⟨w,rfl⟩ := hr w
    exact ⟨S.mkQ w,rfl⟩
  have hd := (LinearEquiv.ofBijective j ⟨hi,hj⟩).finrank_eq
  rw [hs] at hd
  have hp := Atlas.G2.Natural.BinaryPointFlag.card_hyperplane
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hp
  have hp5 : Module.finrank (ZMod 2) Atlas.G2.Natural.BinaryPointFlag.hyperplane = 5 :=
    Nat.pow_right_injective (by decide : 1 < 2) hp
  have hadd := Atlas.G2.Natural.BinaryPointFlag.hyperplane.finrank_quotient_add_finrank
  change Module.finrank (ZMod 2)
    ((Fin 6 → ZMod 2) ⧸ Atlas.G2.Natural.BinaryPointFlag.hyperplane) +
      Module.finrank (ZMod 2) Atlas.G2.Natural.BinaryPointFlag.hyperplane =
      Module.finrank (ZMod 2) (Fin 6 → ZMod 2) at hadd
  have h6 : Module.finrank (ZMod 2) (Fin 6 → ZMod 2) = 6 := by simp
  rw [hp5,h6] at hadd
  omega

open G2Exclusion.MarkedGeometry.LocalParabolics.ThreeOffenderOrbit
open Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.DynkinExclusion.OrbitInvariance

/-- In the selected nonoffender case the literal reciprocal core has index two.
Its image is the natural point hyperplane on the same point-centralizer marking. -/
theorem source_nonoffender_core_hyperplane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (hcomponent : ((K F).subgroupOf F.H).IsCComponent)
    (hfit : Theory.GroupTheory.generalizedFitting (HStar F.H) = star F (K F))
    (eK : ((K F) ⧸ pCore 2 (K F)) ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hf : Function.Injective σ) (hcomm : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1)
    (P : Sylow 2 (HStar F.H)) (hP : star F (K F) ⊔ (P : Subgroup (HStar F.H)) = ⊤)
    (orbit : letI : (star F (K F)).Normal := hfit ▸ inferInstance
      letI : Finite W := Finite.of_surjective (fun x : F.U => (c.coordinates x).toAdd)
        (Multiplicative.toAdd.surjective.comp c.onto)
      OrbitInputs σ (star F (K F)) P hP)
    (path : CriticalPath (L := L) F) (hplace : path.Uα ≤ F.Ri L 1)
    (selection : path.RankSelection) (hn : ¬ IsOffender σ (star F path.Uα)) :
    (F.U ⊓ path.Qα).relIndex F.U = 2 ∧ Nat.card (star F path.Uα) = 4 ∧
    ∃ (f : HStar F.H →* Atlas.G2.Model (ZMod 2))
      (q : W →ₗ[ZMod 2] Atlas.G2.Natural.Space (ZMod 2)),
      Function.Injective f ∧ commutator (Atlas.G2.Model (ZMod 2)) ≤ f.range ∧
      Function.Surjective q ∧
      (∀ a v, q (σ a v) = Atlas.G2.Natural.action (ZMod 2) (f a) (q v)) ∧
      (∀ a v, σ a v = v ↔ Atlas.G2.Natural.action (ZMod 2) (f a) (q v) = q v) ∧
      (star F (F.H ⊓ centralizer (path.Zα : Set G))).map f =
        Atlas.G2.BinaryCore.secondParabolic ⊓ f.range ∧
      (star F path.Uα).map f = Atlas.G2.BinaryCore.natural ∧
      (c.imageSpace (F.U ⊓ path.Qα)).map
        ((Atlas.G2.Restricted.NaturalCoordinates.equiv (ZMod 2)).toLinearMap.comp q) =
        Atlas.G2.Natural.BinaryPointFlag.hyperplane ∧
      ∃ t : F.U, (t : G) ∈ path.Zα ∧
        Atlas.G2.Restricted.NaturalCoordinates.equiv (ZMod 2) (q (c.coordinates t).toAdd) =
          Pi.single 0 1 := by
  let : Finite W := Finite.of_surjective (fun x : F.U => (c.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  obtain ⟨f,q,hf',hJ,hq,he,hfix,hC,hA,hrank,t,ht,hqt⟩ :=
    source_nonoffender_point_actor c h hab hcomponent hfit eK structural hf hcomm P hP orbit
      path hplace selection hn
  have hhyper := nonoffender_core_hyperplane_of_marking c h hab structural hf
    path hplace selection hn f hJ q hq he hfix hC hA t ht hqt
  have hAH : path.Uα ≤ F.H := hplace.trans
    ((pCoreIn_le 2 (F.Li L 1 ⊔ (T : Subgroup G))).trans
      (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)))
  have hpre : commutatorPreimage F.U path.Uα (F.Vi 1) ≤ F.U ⊓ path.Qα := by
    obtain ⟨hquad,hbound⟩ := source_selected_critical_bound c h hab structural hf path selection
    obtain ⟨i,hi,_,hmodels⟩ := source_natural_or_weyl c h hab hcomponent hfit eK hf
      P hP orbit path hplace selection hquad hbound
    rcases hmodels with ⟨E,hE⟩ | ⟨E,hE⟩
    · exact source_critical_fixed_preimage_le_reciprocal_core c h hab path .natural E i hi hE
    · exact source_critical_fixed_preimage_le_reciprocal_core c h hab path .weyl E i hi hE
  have hfixed : fixedSpace σ (star F path.Uα) ≤ c.imageSpace (F.U ⊓ path.Qα) := by
    have hh := c.fixed_image_eq path.Uα hAH c.section_le
    rw [fixedSpace_comp_map] at hh
    change c.imageSpace (commutatorPreimage F.U path.Uα (F.Vi 1)) =
      fixedSpace σ (star F path.Uα) at hh
    rw [←hh]
    exact c.imageSpace_mono hpre
  let r := (Atlas.G2.Restricted.NaturalCoordinates.equiv (ZMod 2)).toLinearMap.comp q
  have hr : Function.Surjective r :=
    (Atlas.G2.Restricted.NaturalCoordinates.equiv (ZMod 2)).surjective.comp hq
  have hk : r.ker ≤ c.imageSpace (F.U ⊓ path.Qα) := by
    intro v hv
    apply hfixed
    have hqv : q v = 0 := (Atlas.G2.Restricted.NaturalCoordinates.equiv (ZMod 2)).injective
      (show _ = _ from hv.trans (map_zero _).symm)
    intro a
    exact (hfix a v).mpr (by rw [hqv,map_zero])
  have hdim := hyperplane_image_codimension (c.imageSpace (F.U ⊓ path.Qα)) r hr hk hhyper
  have hlog := critical_core_image_codimension c h hab structural hf path
  have hindex : (F.U ⊓ path.Qα).relIndex F.U = 2 := by
    let := h.chosen.elementary
    let := hab
    let := elementary_U F
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 F.U).to_quotient
      ((F.U ⊓ path.Qα).subgroupOf F.U) |>.exists_card_eq
    have hh : (F.U ⊓ path.Qα).relIndex F.U = 2^n := hn
    rw [hh,Nat.log_pow Nat.one_lt_two] at hlog
    have hn1 : n = 1 := by omega
    rw [hh,hn1]
    rfl
  have hcard : Nat.card (star F path.Uα) = 4 := by
    rw [(critical_elementary h hab path hplace selection).card_eq_two_pow_rank,hrank]
    rfl
  exact ⟨hindex,hcard,f,q,hf',hJ,hq,he,hfix,hC,hA,hhyper,t,ht,hqt⟩

include c in
/-- The literal index calculation excludes a selected nonoffender whose
reciprocal point lies in the original seed. This uses only the earlier
14.7.58 interchange, not the later 14.7.61 reciprocal symmetry. -/
theorem source_offender_of_partner_point_le_seed
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (hcomponent : ((K F).subgroupOf F.H).IsCComponent)
    (hfit : Theory.GroupTheory.generalizedFitting (HStar F.H) = star F (K F))
    (eK : ((K F) ⧸ pCore 2 (K F)) ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hf : Function.Injective σ) (hcomm : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1)
    (P : Sylow 2 (HStar F.H)) (hP : star F (K F) ⊔ (P : Subgroup (HStar F.H)) = ⊤)
    (orbit : letI : (star F (K F)).Normal := hfit ▸ inferInstance
      letI : Finite W := Finite.of_surjective (fun x : F.U => (c.coordinates x).toAdd)
        (Multiplicative.toAdd.surjective.comp c.onto)
      OrbitInputs σ (star F (K F)) P hP)
    (path : CriticalPath (L := L) F) (hplace : path.Uα ≤ F.Ri L 1)
    (selection : path.RankSelection) (hZV : path.Zα ≤ V) :
    IsOffender σ (star F path.Uα) := by
  by_contra hn
  obtain ⟨hindex,hcard,_⟩ := source_nonoffender_core_hyperplane c h hab hcomponent hfit eK
    structural hf hcomm P hP orbit path hplace selection hn
  have hAH : path.Uα ≤ F.H := hplace.trans
    ((pCoreIn_le 2 (F.Li L 1 ⊔ (T : Subgroup G))).trans
      (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)))
  have hh := critical_quotient_order_eq h path hZV hAH
  omega


include c in
/-- The actual critical point cannot lie in the original seed. In the
nonoffender case the index calculation contradicts 14.7.58; in the offender
case the constructed full marking and 14.7.61 symmetry exclude it from U. -/
theorem source_critical_point_not_le_seed
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (hcomponent : ((K F).subgroupOf F.H).IsCComponent)
    (hfit : Theory.GroupTheory.generalizedFitting (HStar F.H) = star F (K F))
    (eK : ((K F) ⧸ pCore 2 (K F)) ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hf : Function.Injective σ) (hcomm : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1)
    (P : Sylow 2 (HStar F.H)) (hP : star F (K F) ⊔ (P : Subgroup (HStar F.H)) = ⊤)
    (orbit : letI : (star F (K F)).Normal := hfit ▸ inferInstance
      letI : Finite W := Finite.of_surjective (fun x : F.U => (c.coordinates x).toAdd)
        (Multiplicative.toAdd.surjective.comp c.onto)
      OrbitInputs σ (star F (K F)) P hP)
    (path : CriticalPath (L := L) F) (hplace : path.Uα ≤ F.Ri L 1)
    (selection : path.RankSelection) : ¬ path.Zα ≤ V := by
  intro hZV
  have ho := source_offender_of_partner_point_le_seed c h hab hcomponent hfit eK structural
    hf hcomm P hP orbit path hplace selection hZV
  obtain ⟨hquad,hbound⟩ := source_selected_critical_bound c h hab structural hf path selection
  obtain ⟨i,hi,_,hmodels⟩ := source_natural_or_weyl c h hab hcomponent hfit eK hf
    P hP orbit path hplace selection hquad hbound
  have hm : ∃ m : BinaryG2Module, ∃ E : m.Space ≃ₗ[ZMod 2] W,
      ∀ a v, E (m.action (i a) v) = σ a (E v) := by
    rcases hmodels with ⟨E,he⟩ | ⟨E,he⟩
    · exact ⟨.natural,E,he⟩
    · exact ⟨.weyl,E,he⟩
  obtain ⟨m,E,he⟩ := hm
  obtain ⟨p,hA⟩ := model_offender_fullCentralizer m _
    (ho.map_equivariant σ m.action i hi E.symm
      (fun a v => by rw [← E.apply_symm_apply v,← he,E.symm_apply_apply,E.symm_apply_apply]))
  have hnot := (source_full_actor_reciprocity c h hab hcomponent hfit eK structural hf hcomm
    path hplace selection m E i hi he p hA).2.1
  exact hnot (hZV.trans (le_conjugateSpanBy V F.H))

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source
