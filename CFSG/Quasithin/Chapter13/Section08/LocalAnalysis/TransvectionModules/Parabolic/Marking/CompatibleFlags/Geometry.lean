module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.CompatibleFlags.Transport

/-!
# The simultaneous point and plane marking

The image of the actual ambient Sylow subgroup is Sylow in the permutation
image. Conjugating a canonical alternating flag subgroup into it determines
both natural flags by their dimensions and invariance.

In the augmentation cover, a weight-four vector whose small flag orbit has
at most three nonzero elements lies in the canonical plane. The actual
identity V₃ = ⟨V₂^J⟩ transports to generation in weight four. Together with
dimension two and Sylow invariance this determines the plane, and proves
that every nonzero vector has weight four before taking the natural quotient.
All finite certificates use kernel reduction.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 13.7.6(3),
printed pp.938–939, the first paragraph of 13.8.6, printed p.948, and §B.3,
printed pp.83–85. The full compatible permutation action is an input here;
the companion `Assembly` module constructs it from component compatibility
in both cases. The section-generation identity, dimensions and normalizers
remain explicit earlier-source inputs.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.Marking.CompatibleFlags
open scoped IsMulCommutative
open Subgroup Module BinaryPermutation
open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry

private def coordinateSwap : Equiv.Perm (Fin 6) := Equiv.swap 0 4 * Equiv.swap 1 5

private theorem map_flag_borel :
    (H1 ⊓ H2).map (MulAut.conj coordinateSwap).toMonoidHom = borel := by
  have hp : coordinateSwap • pair 4 5 = pair 0 1 := by decide
  have hs : coordinateSwap • baseSyntheme = baseSyntheme := by decide
  rw [Subgroup.map_inf _ _ _ (MulAut.conj coordinateSwap).injective]
  change (MulAction.stabilizer S (pair 4 5)).map _ ⊓
    (MulAction.stabilizer S baseSyntheme).map _ = borel
  rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj,
    ← MulAction.stabilizer_smul_eq_stabilizer_map_conj, hp, hs]
  rfl

private theorem T0_isPGroup : IsPGroup 2 T0 := by
  have hb : IsPGroup 2 borel := borelSylow.isPGroup'
  have hm : (H1 ⊓ H2) ≤ borel.comap (MulAut.conj coordinateSwap).toMonoidHom :=
    Subgroup.map_le_iff_le_comap.mp map_flag_borel.le
  exact (hb.comap_of_injective _ (MulAut.conj coordinateSwap).injective).to_le
    (inf_le_left.trans hm)

/-- A Sylow subgroup in any permutation overgroup of the marked alternating
component contains a conjugate of the canonical alternating flag group. -/
theorem exists_conjugate_T0_le (S : Subgroup (Equiv.Perm (Fin 6)))
    (hS : alternatingGroup (Fin 6) ≤ S) (Q : Sylow 2 S) :
    ∃ g : S, T0.map (MulAut.conj (g : Equiv.Perm (Fin 6))).toMonoidHom ≤
      (Q : Subgroup S).map S.subtype := by
  have hT : T0 ≤ S := inf_le_right.trans hS
  obtain ⟨R, hR⟩ := (T0_isPGroup.comap_subtype (K := S)).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S R Q
  have hc : (R : Subgroup S).map (MulAut.conj g).toMonoidHom = Q :=
    congrArg (fun U : Sylow 2 S => (U : Subgroup S)) hg
  refine ⟨g, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  let tS : S := ⟨t, hT ht⟩
  have htR : tS ∈ R := hR ht
  have htQ : g * tS * g⁻¹ ∈ Q := by
    change g * tS * g⁻¹ ∈ (Q : Subgroup S)
    rw [← hc]
    exact Subgroup.mem_map_of_mem _ htR
  exact ⟨g * tS * g⁻¹, htQ, rfl⟩

/-- Use the actual ambient Sylow subgroup, first inside H and then in the
range of the given quotient action. No Sylow image is assumed. -/
theorem source_sylow_alignment {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) (T : Sylow 2 G) (hTH : (T : Subgroup G) ≤ H)
    (φ : Source.Hstar H →* Equiv.Perm (Fin 6))
    (ha : alternatingGroup (Fin 6) ≤ φ.range) :
    ∃ g : Equiv.Perm (Fin 6), g ∈ φ.range ∧
      T0.map (MulAut.conj g).toMonoidHom ≤
        ((T : Subgroup G).subgroupOf H).map
          (φ.comp (QuotientGroup.mk' (pCore 2 H))) := by
  let f := φ.comp (QuotientGroup.mk' (pCore 2 H))
  have hf : f.range = φ.range := by
    ext a
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨a, rfl⟩
      obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) a
      exact ⟨h, rfl⟩
  let Q := (T.subtype hTH).mapSurjective f.rangeRestrict_surjective
  obtain ⟨g, hg⟩ := exists_conjugate_T0_le f.range (by rwa [hf]) Q
  refine ⟨g, by simpa [hf] using g.property, ?_⟩
  simpa only [Q, Sylow.coe_mapSurjective, Sylow.coe_subtype, Subgroup.map_map,
    MonoidHom.subtype_comp_rangeRestrict] using hg

private local instance : DecidablePred (fun v : Full (Fin 6) => v ∈ core (Fin 6)) :=
  fun v => inferInstanceAs (Decidable ((augmentation (Fin 6)) v = 0))
private local instance : Fintype (core (Fin 6)) :=
  Fintype.ofFinset (Finset.univ.filter (fun v => v ∈ core (Fin 6))) (by simp)

private def flagWords : List S :=
  [1, genA, genB, genA * genB, genC, genA * genC, genB * genC, genA * genB * genC]
private def coverOrbit (v : core (Fin 6)) : Finset (core (Fin 6)) :=
  (flagWords.map (fun g => coreRepresentation (Fin 6) g v)).toFinset

private theorem flagWords_mem {g : S} (hg : g ∈ flagWords) : g ∈ T0 := by
  simp only [flagWords, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact T0.one_mem
  · exact genA_mem_T0
  · exact genB_mem_T0
  · exact T0.mul_mem genA_mem_T0 genB_mem_T0
  · exact genC_mem_T0
  · exact T0.mul_mem genA_mem_T0 genC_mem_T0
  · exact T0.mul_mem genB_mem_T0 genC_mem_T0
  · exact T0.mul_mem (T0.mul_mem genA_mem_T0 genB_mem_T0) genC_mem_T0

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem cover_orbit_line_cert : ∀ v : core (Fin 6),
    OrbitModels.weight v = 4 → (coverOrbit v).card ≤ 1 → v = OrbitModels.point := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem cover_orbit_plane_cert : ∀ v : core (Fin 6),
    OrbitModels.weight v = 4 → (coverOrbit v).card ≤ 3 →
      v = OrbitModels.point ∨ v = OrbitModels.seed ∨
        v = OrbitModels.point + OrbitModels.seed := by
  decide +kernel

private theorem cover_orbit_card_bound (W : Submodule (ZMod 2) (core (Fin 6)))
    (hW : ∀ g ∈ T0, ∀ v ∈ W, coreRepresentation (Fin 6) g v ∈ W)
    (v : core (Fin 6)) (hv : v ∈ W) (hne : v ≠ 0) :
    (coverOrbit v).card + 1 ≤ 2 ^ finrank (ZMod 2) W := by
  classical
  have horbit (x : core (Fin 6)) (hx : x ∈ coverOrbit v) : x ∈ W ∧ x ≠ 0 := by
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
    refine ⟨hW g (flagWords_mem hg) v hv, ?_⟩
    intro h
    apply hne
    have hi := congrArg (coreRepresentation (Fin 6) g⁻¹) h
    simpa only [map_zero, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, Module.End.one_apply] using hi
  let f : Option {x // x ∈ coverOrbit v} → W := fun x => match x with
    | none => ⟨0, W.zero_mem⟩
    | some x => ⟨x.val, (horbit x.val x.property).1⟩
  have hf : Function.Injective f := by
    intro a b hab
    have hab' := congrArg Subtype.val hab
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some b => exact False.elim ((horbit b.val b.property).2 hab'.symm)
    | some a =>
      cases b with
      | none => exact False.elim ((horbit a.val a.property).2 hab')
      | some b => exact congrArg some (Subtype.ext hab')
  let : Fintype W := Fintype.ofFinite W
  have hc := Fintype.card_le_of_injective f hf
  rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := W), ZMod.card] at hc
  simpa only [Fintype.card_option, Fintype.card_coe] using hc

/-- A Sylow-invariant binary point generated in weight four is the marked
point in the cover. -/
theorem cover_point_unique (W : Submodule (ZMod 2) (core (Fin 6)))
    (hdim : finrank (ZMod 2) W = 1)
    (hW : ∀ g ∈ T0, ∀ v ∈ W, coreRepresentation (Fin 6) g v ∈ W)
    (hgen : W = Submodule.span (ZMod 2) {v | v ∈ W ∧ OrbitModels.weight v = 4}) :
    W = OrbitModels.pointSpace := by
  apply Submodule.eq_of_le_of_finrank_eq _ (hdim.trans OrbitModels.pointSpace_finrank.symm)
  conv_lhs => rw [hgen]
  apply Submodule.span_le.mpr
  rintro v ⟨hv, hw⟩
  have hne : v ≠ 0 := by intro h; subst v; simp [OrbitModels.weight] at hw
  have hc := cover_orbit_card_bound W hW v hv hne
  rw [hdim] at hc
  rw [cover_orbit_line_cert v hw (by omega)]
  exact Submodule.subset_span (by simp)

/-- Dimension, Sylow invariance and generation in weight four determine the
actual two-dimensional cover plane. The generation condition excludes the
plane containing the constant vector. -/
theorem cover_plane_unique (W : Submodule (ZMod 2) (core (Fin 6)))
    (hdim : finrank (ZMod 2) W = 2)
    (hW : ∀ g ∈ T0, ∀ v ∈ W, coreRepresentation (Fin 6) g v ∈ W)
    (hgen : W = Submodule.span (ZMod 2) {v | v ∈ W ∧ OrbitModels.weight v = 4}) :
    W = OrbitModels.plane := by
  apply Submodule.eq_of_le_of_finrank_eq _ (hdim.trans OrbitModels.plane_finrank.symm)
  conv_lhs => rw [hgen]
  apply Submodule.span_le.mpr
  rintro v ⟨hv, hw⟩
  have hne : v ≠ 0 := by intro h; subst v; simp [OrbitModels.weight] at hw
  have hc := cover_orbit_card_bound W hW v hv hne
  rw [hdim] at hc
  rcases cover_orbit_plane_cert v hw (by omega) with rfl | rfl | rfl
  · exact Submodule.subset_span (by simp)
  · exact Submodule.subset_span (by simp)
  · exact Submodule.add_mem _ (Submodule.subset_span (by simp))
      (Submodule.subset_span (by simp))

/-- Coordinate permutations retain the cover weight, before taking the natural quotient. -/
theorem cover_weight_map (g : Equiv.Perm (Fin 6)) (v : core (Fin 6)) :
    OrbitModels.weight (coreRepresentation (Fin 6) g v) = OrbitModels.weight v := by
  change (Finset.univ.filter (fun i => v.val (g.symm i) ≠ 0)).card =
    (Finset.univ.filter (fun i => v.val i ≠ 0)).card
  apply Finset.card_bij (fun i _ => g.symm i)
  · intro i hi
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi
  · intro a ha b hb hab
    exact g.symm.injective hab
  · intro b hb
    refine ⟨g b, ?_, by simp⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply] using hb

/-- Generation by weight-four vectors is unchanged by a coordinate permutation. -/
theorem cover_weight_generation_map (P : Submodule (ZMod 2) (core (Fin 6)))
    (hP : P = Submodule.span (ZMod 2) {v | v ∈ P ∧ OrbitModels.weight v = 4})
    (g : Equiv.Perm (Fin 6)) :
    P.map (coreRepresentation (Fin 6) g) = Submodule.span (ZMod 2)
      {v | v ∈ P.map (coreRepresentation (Fin 6) g) ∧ OrbitModels.weight v = 4} := by
  apply le_antisymm
  · conv_lhs => rw [hP, Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨v, ⟨hv, hw⟩, rfl⟩
    exact Submodule.subset_span ⟨Submodule.mem_map_of_mem hv, (cover_weight_map g v).trans hw⟩
  · apply Submodule.span_le.mpr
    exact fun _ h => h.1

/-- Conjugate the canonical flag subgroup into an actual Sylow image, then
pull an invariant subspace back by the same coordinate permutation. -/
theorem invariant_after_alignment {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (r : Representation (ZMod 2) S W) (P : Submodule (ZMod 2) W)
    (J : Subgroup S) (g : S)
    (hg : T0.map (MulAut.conj g).toMonoidHom ≤ J)
    (hP : ∀ j ∈ J, ∀ v ∈ P, r j v ∈ P) :
    ∀ t ∈ T0, ∀ v ∈ P.map (r g⁻¹), r t v ∈ P.map (r g⁻¹) := by
  intro t ht v hv
  obtain ⟨u, hu, rfl⟩ := hv
  refine ⟨r (g * t * g⁻¹) u,
    hP _ (hg (Subgroup.mem_map_of_mem _ ht)) u hu, ?_⟩
  simp only [← Module.End.mul_apply, ← map_mul]
  congr 2
  group

/-- The source group normalizer gives invariance of the marked section under
the actual image of T. -/
theorem marked_section_invariant {G W : Type*} [Group G]
    [AddCommGroup W] [Module (ZMod 2) W]
    {H V₃ V₁ : Subgroup G} [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : TransvectionRecognition.IsConjugation H V₃ V₁ ρ)
    (φ : Source.Hstar H →* S) (r : Representation (ZMod 2) S W)
    (E : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] W)
    (he : ∀ a u, E (ρ a u) = r (φ a) (E u))
    (T X : Subgroup G) (hTX : T ≤ normalizer (X : Set G)) :
    ∀ g ∈ (T.subgroupOf H).map (φ.comp (QuotientGroup.mk' (pCore 2 H))),
      ∀ v ∈ (sectionImage H V₃ V₁ X).map E.toLinearMap,
        r g v ∈ (sectionImage H V₃ V₁ X).map E.toLinearMap := by
  rintro g ⟨t, ht, rfl⟩ v ⟨u, hu, rfl⟩
  change r (φ (QuotientGroup.mk' (pCore 2 H) t)) (E u) ∈ _
  rw [← he]
  exact Submodule.mem_map_of_mem (sectionImage_invariant ρ hρ X t (hTX ht) u hu)

/-- The literal section-generation identity in 13.7.6 transports the point's
weight-four witness to generation of the cover plane in weight four. No equality
of the preimage groups is required. -/
theorem cover_weight_generation_of_section_span {G : Type*} [Group G]
    {H V₃ V₂ V₁ : Subgroup G} [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (φ : Source.Hstar H →* S)
    (E : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] core (Fin 6))
    (he : ∀ a u, E (ρ a u) = coreRepresentation (Fin 6) (φ a) (E u))
    (hpoint : (sectionImage H V₃ V₁ V₂).map E.toLinearMap = OrbitModels.pointSpace)
    (J : Subgroup G)
    (hspan : sectionImage H V₃ V₁ V₃ = Submodule.span (ZMod 2)
      {v | ∃ a ∈ Source.starImage H J, ∃ x ∈ sectionImage H V₃ V₁ V₂, ρ a x = v}) :
    let W := (sectionImage H V₃ V₁ V₃).map E.toLinearMap
    W = Submodule.span (ZMod 2) {v | v ∈ W ∧ OrbitModels.weight v = 4} := by
  let W := (sectionImage H V₃ V₁ V₃).map E.toLinearMap
  change W = _
  apply le_antisymm
  · change (sectionImage H V₃ V₁ V₃).map E.toLinearMap ≤ _
    conv_lhs => rw [hspan, Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨a, ha, x, hx, rfl⟩, rfl⟩
    have hEx : E x ∈ OrbitModels.pointSpace := by
      rw [← hpoint]
      exact Submodule.mem_map_of_mem hx
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hEx
    have hm : coreRepresentation (Fin 6) (φ a) OrbitModels.point ∈ W := by
      have hpointmem : OrbitModels.point ∈
          (sectionImage H V₃ V₁ V₂).map E.toLinearMap := by
        rw [hpoint]
        exact Submodule.subset_span (by simp)
      obtain ⟨u, hu, heU⟩ := hpointmem
      change E u = OrbitModels.point at heU
      have hmem : ρ a u ∈ sectionImage H V₃ V₁ V₃ := by
        rw [hspan]
        exact Submodule.subset_span ⟨a, ha, u, hu, rfl⟩
      have hm' := Submodule.mem_map_of_mem (f := E.toLinearMap) hmem
      change E (ρ a u) ∈ W at hm'
      rw [he, heU] at hm'
      exact hm'
    have hg : coreRepresentation (Fin 6) (φ a) OrbitModels.point ∈
        Submodule.span (ZMod 2) {v | v ∈ W ∧ OrbitModels.weight v = 4} :=
      Submodule.subset_span ⟨hm, (cover_weight_map _ _).trans OrbitModels.point_weight⟩
    change E (ρ a x) ∈ _
    rw [he, ← hc, map_smul]
    exact Submodule.smul_mem _ c hg
  · exact Submodule.span_le.mpr (fun _ h => h.1)


/-- Actual conjugate generation of V₃ from V₂ yields generation in weight
four in the cover; it does not posit a plane marking. -/
theorem cover_source_weight_generation {G : Type*} [Group G]
    {H V₃ V₂ V₁ : Subgroup G} [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : TransvectionRecognition.IsConjugation H V₃ V₁ ρ)
    (φ : Source.Hstar H →* S)
    (E : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] core (Fin 6))
    (he : ∀ a u, E (ρ a u) = coreRepresentation (Fin 6) (φ a) (E u))
    (hpoint : (sectionImage H V₃ V₁ V₂).map E.toLinearMap = OrbitModels.pointSpace)
    (J : Subgroup G) (hJ : J ≤ H) (hV₂ : V₂ ≤ Source.UH H V₃)
    (hgen : V₃ = conjugateSpanBy V₂ J) :
    let W := (sectionImage H V₃ V₁ V₃).map E.toLinearMap
    W = Submodule.span (ZMod 2) {v | v ∈ W ∧ OrbitModels.weight v = 4} := by
  have hspan : sectionImage H V₃ V₁ V₃ = Submodule.span (ZMod 2)
      {v | ∃ a ∈ Source.starImage H J, ∃ x ∈ sectionImage H V₃ V₁ V₂, ρ a x = v} :=
    (congrArg (sectionImage H V₃ V₁) hgen).trans
      (sectionImage_conjugateSpan ρ hρ V₂ J hV₂ hJ)
  exact cover_weight_generation_of_section_span ρ φ E he hpoint J hspan

private theorem invariant_map_eq {A W : Type*} [Group A] [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : Representation (ZMod 2) A W)
    (J : Subgroup A) (P : Submodule (ZMod 2) W)
    (hi : ∀ a ∈ J, ∀ v ∈ P, ρ a v ∈ P) (a : A) (ha : a ∈ J) :
    P.map (ρ a) = P := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    exact hi a ha v hv
  · intro v hv
    refine ⟨ρ a⁻¹ v, hi a⁻¹ (J.inv_mem ha) v hv, ?_⟩
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

/-- Both natural flags are marked by one permutation chosen from the actual
Sylow image. The plane is determined by its dimension and invariance. -/
theorem natural_source_flags {G : Type*} [Group G] [Finite G]
    {H V₃ V₂ V₁ : Subgroup G} [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    (T : Sylow 2 G) (hTH : (T : Subgroup G) ≤ H)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : TransvectionRecognition.IsConjugation H V₃ V₁ ρ)
    (φ : Source.Hstar H →* S) (ha : alternatingGroup (Fin 6) ≤ φ.range)
    (E : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] natural (Fin 6))
    (he : ∀ a u, E (ρ a u) = naturalRepresentation (Fin 6) (φ a) (E u))
    (hTV₂ : (T : Subgroup G) ≤ normalizer (V₂ : Set G))
    (hTV₃ : (T : Subgroup G) ≤ normalizer (V₃ : Set G))
    (hdim₂ : finrank (ZMod 2) (sectionImage H V₃ V₁ V₂) = 1)
    (hdim₃ : finrank (ZMod 2) (sectionImage H V₃ V₁ V₃) = 2) :
    ∃ g : S, g ∈ φ.range ∧
      ((sectionImage H V₃ V₁ V₂).map E.toLinearMap).map
        (naturalRepresentation (Fin 6) g⁻¹) = OrbitModels.naturalPointSpace ∧
      ((sectionImage H V₃ V₁ V₃).map E.toLinearMap).map
        (naturalRepresentation (Fin 6) g⁻¹) =
          OrbitModels.plane.map (coreToNatural (Fin 6)) := by
  obtain ⟨g, hg, halign⟩ := source_sylow_alignment H T hTH φ ha
  let r := naturalRepresentation (Fin 6)
  let e := LinearMap.GeneralLinearGroup.toLinearEquiv (r.asGroupHom g⁻¹)
  let P := (sectionImage H V₃ V₁ V₂).map E.toLinearMap
  let D := (sectionImage H V₃ V₁ V₃).map E.toLinearMap
  have hi (X : Subgroup G) (hTX : (T : Subgroup G) ≤ normalizer (X : Set G)) :=
    invariant_after_alignment r ((sectionImage H V₃ V₁ X).map E.toLinearMap)
      _ g halign (marked_section_invariant ρ hρ φ r E he _ X hTX)
  refine ⟨g, hg, ?_, ?_⟩
  · have hp : P.map (r g⁻¹) = canonicalLine := by
      apply canonicalLine_unique
      · exact (e.finrank_map_eq P).trans ((E.finrank_map_eq _).trans hdim₂)
      · exact invariant_map_eq r T0 _ (hi V₂ hTV₂)
    simpa only [canonicalLine, OrbitModels.naturalPointSpace,
      naturalPoint_eq_pairVector] using hp
  · rw [plane_image_eq_canonical]
    apply canonicalPlane_unique
    · exact (e.finrank_map_eq D).trans ((E.finrank_map_eq _).trans hdim₃)
    · exact invariant_map_eq r T0 _ (hi V₃ hTV₃)

/-- Simultaneously mark both cover flags using precisely the section-generation
identity printed in 13.7.6. Dimension and Sylow invariance determine the plane;
every nonzero vector has weight four in the actual cover. -/
theorem augmentation_flags_of_section_span {G : Type*} [Group G] [Finite G]
    {H V₃ V₂ V₁ : Subgroup G} [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    (T : Sylow 2 G) (hTH : (T : Subgroup G) ≤ H)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : TransvectionRecognition.IsConjugation H V₃ V₁ ρ)
    (φ : Source.Hstar H →* S) (ha : alternatingGroup (Fin 6) ≤ φ.range)
    (E : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] core (Fin 6))
    (he : ∀ a u, E (ρ a u) = coreRepresentation (Fin 6) (φ a) (E u))
    (hpoint : (sectionImage H V₃ V₁ V₂).map E.toLinearMap = OrbitModels.pointSpace)
    (hTV₂ : (T : Subgroup G) ≤ normalizer (V₂ : Set G))
    (hTV₃ : (T : Subgroup G) ≤ normalizer (V₃ : Set G))
    (hdim₃ : finrank (ZMod 2) (sectionImage H V₃ V₁ V₃) = 2)
    (J : Subgroup G)
    (hspan : sectionImage H V₃ V₁ V₃ = Submodule.span (ZMod 2)
      {v | ∃ a ∈ Source.starImage H J, ∃ x ∈ sectionImage H V₃ V₁ V₂, ρ a x = v}) :
    ∃ g : S, g ∈ φ.range ∧
      ((sectionImage H V₃ V₁ V₂).map E.toLinearMap).map
        (coreRepresentation (Fin 6) g⁻¹) = OrbitModels.pointSpace ∧
      ((sectionImage H V₃ V₁ V₃).map E.toLinearMap).map
        (coreRepresentation (Fin 6) g⁻¹) = OrbitModels.plane ∧
      (∀ v ∈ (sectionImage H V₃ V₁ V₃).map E.toLinearMap,
        v ≠ 0 → OrbitModels.weight v = 4) := by
  obtain ⟨g, hg, halign⟩ := source_sylow_alignment H T hTH φ ha
  let r := coreRepresentation (Fin 6)
  let e := LinearMap.GeneralLinearGroup.toLinearEquiv (r.asGroupHom g⁻¹)
  let P := (sectionImage H V₃ V₁ V₂).map E.toLinearMap
  let D := (sectionImage H V₃ V₁ V₃).map E.toLinearMap
  have hi (X : Subgroup G) (hTX : (T : Subgroup G) ≤ normalizer (X : Set G)) :=
    invariant_after_alignment r ((sectionImage H V₃ V₁ X).map E.toLinearMap)
      _ g halign (marked_section_invariant ρ hρ φ r E he _ X hTX)
  have hPgen : P = Submodule.span (ZMod 2) {v | v ∈ P ∧ OrbitModels.weight v = 4} := by
    dsimp only [P]
    rw [hpoint]
    apply le_antisymm
    · change Submodule.span (ZMod 2) {OrbitModels.point} ≤ _
      apply Submodule.span_le.mpr
      rintro v rfl
      exact Submodule.subset_span ⟨Submodule.subset_span (by simp), OrbitModels.point_weight⟩
    · exact Submodule.span_le.mpr (fun _ h => h.1)
  have hp : P.map (r g⁻¹) = OrbitModels.pointSpace := by
    apply cover_point_unique
    · apply (e.finrank_map_eq P).trans
      change finrank (ZMod 2) ((sectionImage H V₃ V₁ V₂).map E.toLinearMap) = 1
      rw [hpoint]
      exact OrbitModels.pointSpace_finrank
    · exact hi V₂ hTV₂
    · exact cover_weight_generation_map P hPgen g⁻¹
  have hd : D.map (r g⁻¹) = OrbitModels.plane := by
    apply cover_plane_unique
    · exact (e.finrank_map_eq D).trans ((E.finrank_map_eq _).trans hdim₃)
    · exact hi V₃ hTV₃
    · exact cover_weight_generation_map D
        (cover_weight_generation_of_section_span ρ φ E he hpoint J hspan) g⁻¹
  refine ⟨g, hg, hp, hd, ?_⟩
  intro v hv hne
  have hm : e v ∈ OrbitModels.plane := by
    rw [← hd]
    exact Submodule.mem_map_of_mem hv
  have hn : e v ≠ 0 := by
    intro h
    apply hne
    exact e.injective (h.trans e.map_zero.symm)
  have hw := OrbitModels.plane_weight (e v) hm hn
  exact (cover_weight_map g⁻¹ v).symm.trans hw


/-- The cover flags use the earlier weight-four point witness and the actual
identity V₃ = ⟨V₂^J⟩. Generation and dimension prove the plane marking and
all its weight-four assertions, in the cover itself. -/
theorem augmentation_source_flags {G : Type*} [Group G] [Finite G]
    {H V₃ V₂ V₁ : Subgroup G} [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    (T : Sylow 2 G) (hTH : (T : Subgroup G) ≤ H)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : TransvectionRecognition.IsConjugation H V₃ V₁ ρ)
    (φ : Source.Hstar H →* S) (ha : alternatingGroup (Fin 6) ≤ φ.range)
    (E : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] core (Fin 6))
    (he : ∀ a u, E (ρ a u) = coreRepresentation (Fin 6) (φ a) (E u))
    (hpoint : (sectionImage H V₃ V₁ V₂).map E.toLinearMap = OrbitModels.pointSpace)
    (hTV₂ : (T : Subgroup G) ≤ normalizer (V₂ : Set G))
    (hTV₃ : (T : Subgroup G) ≤ normalizer (V₃ : Set G))
    (hdim₃ : finrank (ZMod 2) (sectionImage H V₃ V₁ V₃) = 2)
    (J : Subgroup G) (hJ : J ≤ H) (hV₂ : V₂ ≤ Source.UH H V₃)
    (hgen : V₃ = conjugateSpanBy V₂ J) :
    ∃ g : S, g ∈ φ.range ∧
      ((sectionImage H V₃ V₁ V₂).map E.toLinearMap).map
        (coreRepresentation (Fin 6) g⁻¹) = OrbitModels.pointSpace ∧
      ((sectionImage H V₃ V₁ V₃).map E.toLinearMap).map
        (coreRepresentation (Fin 6) g⁻¹) = OrbitModels.plane ∧
      (∀ v ∈ (sectionImage H V₃ V₁ V₃).map E.toLinearMap,
        v ≠ 0 → OrbitModels.weight v = 4) := by
  have hspan : sectionImage H V₃ V₁ V₃ = Submodule.span (ZMod 2)
      {v | ∃ a ∈ Source.starImage H J, ∃ x ∈ sectionImage H V₃ V₁ V₂, ρ a x = v} :=
    (congrArg (sectionImage H V₃ V₁) hgen).trans
      (sectionImage_conjugateSpan ρ hρ V₂ J hV₂ hJ)
  exact augmentation_flags_of_section_span T hTH ρ hρ φ ha E he hpoint
    hTV₂ hTV₃ hdim₃ J hspan

end CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.Marking.CompatibleFlags
