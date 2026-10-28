module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.FFSource
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesComplete
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.DoubledOrbitCover
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.OrbitTransport
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.SymplecticFour.Coordinates
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.NormalSupplementModels

/-!
# Full-orbit FF exclusion for the rank-two source branch

The chosen module is first extended to its literal Sylow orbit using the proved
source 3.2.5 alternatives. The doubled natural-plus-dual branch is converted
back to the binary containing quotient and excluded by the existing source
component sieve. The natural SL₃ and Sp₄ branches are excluded by their two
invariant parabolics and the original minimal-parabolic hypothesis. All maps
are the literal chosen central quotient and ambient conjugation maps.

Source: Aschbacher--Smith 3.2.5, B.6.9 and 11.3.5, printed pp.580,116,771.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.QuasisimpleNormalizer
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
open ChapterB.QuasisimpleSource
namespace Models
open Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K W : Subgroup G}

private def wholeSpace (E : ChosenModule T K W)
    (hT : (T : Subgroup G) ≤ normalizer (W : Set G)) :
    Subrepresentation (reducedRepresentation (K ⊔ (T : Subgroup G))) where
  toSubmodule := E.space
  apply_mem_toSubmodule := by
    have hn := sup_le E.normalizes hT
    have hi : (⊤ : Subgroup (K ⊔ (T : Subgroup G) : Subgroup G)) ≤
        subspaceStabilizer (reducedRepresentation (K ⊔ (T : Subgroup G))) E.space := by
      intro g _
      apply (subspace_map_eq_iff _ _ _).mp
      apply ReducedNormal.subspaceImage_injective
      change ReducedNormal.subspaceImage _ (E.space.map (ReducedNormal.representation _ g)) = _
      rw [ReducedNormal.subspaceImage_map,show ReducedNormal.subspaceImage _ E.space = W from E.image_eq]
      exact mem_normalizer_iff_map_conj_eq.mp (hn g.property)
    intro g v hv
    exact (hi (mem_top g) v).mpr hv

private def wholeAction (E : ChosenModule T K W)
    (hT : (T : Subgroup G) ≤ normalizer (W : Set G)) :
    Representation (ZMod 2) (K ⊔ (T : Subgroup G) : Subgroup G) E.space :=
  (wholeSpace E hT).toRepresentation

omit [Finite G] in
private theorem wholeAction_component (E : ChosenModule T K W)
    (hT : (T : Subgroup G) ≤ normalizer (W : Set G))
    (k : K.subgroupOf (K ⊔ (T : Subgroup G))) :
    wholeAction E hT k = E.chosenAction ((subgroupOfEquivOfLe le_sup_left) k) := rfl

private def wholeCentral (E : ChosenModule T K W)
    (hT : (T : Subgroup G) ≤ normalizer (W : Set G)) :
    Subrepresentation (wholeAction E hT) where
  toSubmodule := (fixedSpace (reducedRepresentation (K ⊔ (T : Subgroup G)))
    (K.subgroupOf (K ⊔ (T : Subgroup G)))).comap E.space.subtype
  apply_mem_toSubmodule := by
    let B := K.subgroupOf (K ⊔ (T : Subgroup G))
    let : B.Normal := normal_subgroupOf_of_le_normalizer
      (sup_le K.le_normalizer E.sylow_normalizes_component)
    have he : fixedSpace (wholeAction E hT) B =
        (fixedSpace (reducedRepresentation (K ⊔ (T : Subgroup G))) B).comap E.space.subtype := by
      ext v
      constructor
      · intro hv k
        exact congrArg Subtype.val (hv k)
      · intro hv k
        exact Subtype.ext (hv k)
    intro g v hv
    rw [← he] at hv ⊢
    exact (fixedSubrepresentation (wholeAction E hT) B).apply_mem_toSubmodule g hv

private def wholeCentralAction (E : ChosenModule T K W)
    (hT : (T : Subgroup G) ≤ normalizer (W : Set G)) :
    Representation (ZMod 2) (K ⊔ (T : Subgroup G) : Subgroup G) E.chosenCentralQuotient :=
  (wholeCentral E hT).quotientRepresentation

omit [Finite G] in
private theorem wholeCentralAction_component (E : ChosenModule T K W)
    (hT : (T : Subgroup G) ≤ normalizer (W : Set G))
    (k : K.subgroupOf (K ⊔ (T : Subgroup G))) :
    wholeCentralAction E hT k = E.chosenCentralAction ((subgroupOfEquivOfLe le_sup_left) k) := by
  apply LinearMap.ext
  intro v
  induction v using Submodule.Quotient.induction_on with
  | _ v => rfl

variable {X Q Y : Type*} [Group X] [Finite X] [Group Q]
  [AddCommGroup Y] [Module (ZMod 2) Y]

omit [Finite X] in
private theorem image_coordinates
    (ρ : Representation (ZMod 2) X Y) (K : Subgroup X)
    (σ : Representation (ZMod 2) Q Y) (hf : Function.Injective σ)
    (q : K →* Q) (hq : Function.Surjective q)
    (he : ∀ k : K, ρ k = σ (q k)) :
    ∃ e : K.map ρ.asGroupHom.rangeRestrict ≃* Q,
      ∀ k : K, e ((ρ.asGroupHom.rangeRestrict.subgroupMap K) k) = q k := by
  let f := ρ.asGroupHom.rangeRestrict.subgroupMap K
  have hk : f.ker = q.ker := by
    ext k
    change f k = 1 ↔ q k = 1
    constructor
    · intro h
      apply hf
      rw [map_one, ← he]
      exact congrArg (fun z : K.map ρ.asGroupHom.rangeRestrict => z.val.val.val) h
    · intro h
      apply Subtype.ext
      apply Subtype.ext
      apply Units.ext
      change ρ k = 1
      rw [he, h, map_one]
  let e : K.map ρ.asGroupHom.rangeRestrict ≃* Q :=
    (QuotientGroup.quotientKerEquivOfSurjective f
      (ρ.asGroupHom.rangeRestrict.subgroupMap_surjective K)).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hk).trans
        (QuotientGroup.quotientKerEquivOfSurjective q hq))
  refine ⟨e, ?_⟩
  intro k
  let E := QuotientGroup.quotientKerEquivOfSurjective f
    (ρ.asGroupHom.rangeRestrict.subgroupMap_surjective K)
  have hE : E (QuotientGroup.mk' f.ker k) = f k := rfl
  change (QuotientGroup.quotientKerEquivOfSurjective q hq)
    ((QuotientGroup.quotientMulEquivOfEq hk) (E.symm (f k))) = q k
  rw [← hE, E.symm_apply_apply]
  rfl

omit [Finite X] in
private theorem image_action_equiv
    (ρ : Representation (ZMod 2) X Y) (K : Subgroup X)
    (σ : Representation (ZMod 2) Q Y) (hf : Function.Injective σ)
    (q : K →* Q) (hq : Function.Surjective q)
    (he : ∀ k : K, ρ k = σ (q k)) :
    Nonempty (ActionEquiv
      ((linearAction ρ.asGroupHom.range).comp (K.map ρ.asGroupHom.rangeRestrict).subtype) σ) := by
  obtain ⟨e,heq⟩ := image_coordinates ρ K σ hf q hq he
  refine ⟨⟨e, LinearEquiv.refl _ _, ?_⟩⟩
  intro k w
  obtain ⟨l,rfl⟩ := ρ.asGroupHom.rangeRestrict.subgroupMap_surjective K k
  change ρ l w = σ (e ((ρ.asGroupHom.rangeRestrict.subgroupMap K) l)) w
  rw [heq,he]

private theorem image_minimal
    (T : Sylow 2 X) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (ρ : Representation (ZMod 2) X Y) (K : Subgroup X)
    (σ : Representation (ZMod 2) Q Y) (hf : Function.Injective σ)
    (q : K →* Q) (hq : Function.Surjective q)
    (he : ∀ k : K, ρ k = σ (q k)) (hs : ¬ Group.IsSolvable Q) :
    ChapterB.IsMinimalParabolicOver (T.mapSurjective ρ.asGroupHom.rangeRestrict_surjective) ⊤ := by
  obtain ⟨e,_⟩ := image_coordinates ρ K σ hf q hq he
  apply ChapterB.minimalParabolic_surjective_of_not_solvable T hP
    ρ.asGroupHom.rangeRestrict ρ.asGroupHom.rangeRestrict_surjective
  intro hh
  let := hh
  exact hs (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)

private theorem no_natural_quotient
    (T : Sylow 2 X) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (B : Subgroup X) [B.Normal] (hgen : B ⊔ (T : Subgroup X) = ⊤)
    (ρ : Representation (ZMod 2) X Y) (σ : Representation (ZMod 2) Q Y)
    (hf : Function.Injective σ) (q : B →* Q) (hq : Function.Surjective q)
    (he : ∀ b : B, ρ b = σ (q b)) (hs : ¬ Group.IsSolvable Q)
    (F : BinaryField) (hF : 1 < F.degree)
    (hm : Nonempty (ActionEquiv σ (linearNatural F 3)) ∨
      Nonempty (ActionEquiv σ (binarySymplectic F))) : False := by
  let a := ρ.asGroupHom.rangeRestrict
  let S := T.mapSurjective ρ.asGroupHom.rangeRestrict_surjective
  let I := B.map a
  let : Finite ρ.asGroupHom.range := Finite.of_surjective _ ρ.asGroupHom.rangeRestrict_surjective
  let : I.Normal := (inferInstance : B.Normal).map a ρ.asGroupHom.rangeRestrict_surjective
  have hg : I ⊔ (S : Subgroup _) = ⊤ := by
    change B.map a ⊔ (T : Subgroup X).map a = _
    rw [← Subgroup.map_sup,hgen,map_top_of_surjective _ ρ.asGroupHom.rangeRestrict_surjective]
  obtain ⟨c⟩ := image_action_equiv ρ B σ hf q hq he
  have hp := image_minimal T hP ρ B σ hf q hq he hs
  rcases hm with hm | hm
  · exact ChapterB.not_minimalParabolic_of_natural_three S I hg
      (linearAction ρ.asGroupHom.range) F ⟨c.trans hm.some⟩ hp
  · let e := c.trans hm.some
    exact ChapterB.not_minimalParabolic_of_symplectic_coordinates S I hg
      (linearAction ρ.asGroupHom.range) e.groupEquiv e.linearEquiv e.intertwines
      (by rw [F.card_eq]; exact (show 2^1 < 2^F.degree from
        Nat.pow_lt_pow_right (by decide) hF)) hp
end Models

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H K J : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

/-- A source seed with a Sylow-invariant natural chosen central quotient would
have two distinct invariant parabolics, contrary to the original minimality. -/
theorem ComponentSeed.not_normalized_natural
    (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hn : (K.subgroupOf H).Normal)
    {W : Subgroup G} (E : Chapter12.Section02.ChosenModule T K W)
    (hT : (T : Subgroup G) ≤ normalizer (W : Set G))
    (F : BinaryField) (hF : 1 < F.degree)
    (hm : Nonempty (ActionEquiv E.centralQuotientAction (linearNatural F 3)) ∨
      Nonempty (ActionEquiv E.centralQuotientAction (binarySymplectic F))) : False := by
  let B := K.subgroupOf H
  let : B.Normal := hn
  let eH : H ≃* (K ⊔ (T : Subgroup G) : Subgroup G) :=
    MulEquiv.subgroupCongr s.supplement.symm
  let ρ := (Models.wholeCentralAction E hT).comp eH.toMonoidHom
  let q : B →* (K ⧸ pCore 2 K) := (QuotientGroup.mk' (pCore 2 K)).comp
    (subgroupOfEquivOfLe s.component.1).toMonoidHom
  have he (b : B) : ρ b = E.centralQuotientAction (q b) := by
    exact Models.wholeCentralAction_component E hT
      ⟨eH b, show ((eH b : (K ⊔ (T : Subgroup G) : Subgroup G)) : G) ∈ K from b.property⟩
  have hf : Function.Injective E.centralQuotientAction := by
    rcases hm with hm | hm
    · intro x y heq
      apply hm.some.groupEquiv.injective
      apply specialLinearNatural_injective 3
      apply LinearMap.ext
      intro v
      obtain ⟨w,rfl⟩ := hm.some.linearEquiv.surjective v
      exact (hm.some.intertwines x w).symm.trans
        ((congrArg hm.some.linearEquiv (LinearMap.congr_fun heq w)).trans
          (hm.some.intertwines y w))
    · intro x y heq
      apply hm.some.groupEquiv.injective
      apply Subtype.ext
      apply Matrix.toLin'.injective
      apply LinearMap.ext
      intro v
      obtain ⟨w,rfl⟩ := hm.some.linearEquiv.surjective v
      exact (hm.some.intertwines x w).symm.trans
        ((congrArg hm.some.linearEquiv (LinearMap.congr_fun heq w)).trans
          (hm.some.intertwines y w))
  let := s.quasisimple
  let : IsSimpleGroup ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) := IsQuasisimple.simple
  let : Nontrivial (K ⧸ pCore 2 K) := (QuotientGroup.mk'_surjective (center (K ⧸ pCore 2 K))).nontrivial
  exact Models.no_natural_quotient (T.subtype h.outside.1.1.2)
    (outside_minimalParabolic h (weakClosure_not_le_core_of_counterexample h pr hc))
    B (s.intrinsic_supplement h.outside.1.1.2) ρ E.centralQuotientAction hf q
    ((QuotientGroup.mk'_surjective _).comp (subgroupOfEquivOfLe s.component.1).surjective)
    he (Group.IsPerfect.not_isSolvable _) F hF hm

/-- The actual FF doubled Sylow orbit gives a small binary containing quotient,
which the original source component has already excluded. -/
theorem ComponentSeed.not_doubled_of_overcomponent_orbit_ff
    (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hJ : J ∈ Chapter1.LStar G (T : Subgroup G)) (hKJ : K ≤ J)
    {W : Subgroup G} (E : Chapter12.Section02.ChosenModule T J W)
    (hsrc : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T J)
    (hff : IsFFModule E.sourceOrbitNormalizerRepresentation) : ¬ E.MarkedDoubled := by
  intro hd
  obtain ⟨n,hn,e,_⟩ := E.doubledOrbit_component_marking hsrc hd hff
  apply s.not_small_binary_linear_overcomponent h pr hc hs hJ.1 hKJ (.inr hn)
  exact ⟨ZMod 2,inferInstance,inferInstance,by simp,
    ⟨(e.trans (BinaryLinear.OuterCyclic.slEquivLinear n).symm).trans
      (BinaryLinear.OuterCyclic.projectiveEquivSL (by omega)).symm⟩⟩

/-- Full-orbit FF now excludes every nonlinear normal seed. The proved 3.2.5
alternatives supply Sylow normalization; no constituent/orbit identification
or extra rank-two exclusion is assumed. -/
theorem ComponentSeed.linear_of_overcomponent_orbit_ff
    (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : (K.subgroupOf H).Normal)
    (hJ : J ∈ Chapter1.LStar G (T : Subgroup G)) (hKJ : K ≤ J)
    {W : Subgroup G} (E : Chapter12.Section02.ChosenModule T J W)
    (hsrc : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J)
    (hff : IsFFModule E.sourceOrbitNormalizerRepresentation) :
    ∃ f : ℕ, 2 ≤ f ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f) := by
  have hnd := s.not_doubled_of_overcomponent_orbit_ff h pr hc hs hJ hKJ E hsrc.toHypothesis1221 hff
  have hT := (E.structural_of_not_doubled_of_many hsrc S.many hnd).1
  have horbit : W = E.sourceOrbit := by
    rw [E.sourceOrbit_eq]
    exact (le_antisymm (iSup_conjugates_le_of_le_normalizer W T W le_rfl hT)
      (le_componentOrbit W T)).symm
  have hff' := (E.chosen_normalizer_ff_iff_orbit_of_eq horbit).mpr hff
  rcases s.normal_source_models_of_overcomponent_ff h pr hc hs hn hJ hKJ E hff' with
    hl | ⟨he,F,hF,hm⟩
  · exact hl
  · subst J
    exact (s.not_normalized_natural h pr hc hn E hT F hF hm).elim

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
