module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Classification.DoubledExclusion
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Classification.Recognition

/-!
# Natural reselection before orienting the field-four triangle

For a chosen module whose actual two-core quotient is Sp₄(4) or G₂(4),
the preceding normalized 7.0.1 alternatives give FF on the entire Sylow
orbit: its actual component order excludes the orthogonal-minus row.
The B.5.1 order comparison then forces that orbit to be Irr⁺. The original
seed is Irr⁺ as well, so its antichain property excludes a doubled orbit.
Source 3.2.5 now fixes the seed, and B.5 recognizes its literal central
quotient as the corresponding natural action over a field of order four.

This extends the checked shadow-reselection argument at its actual group
hypotheses. Neither triangle orientation nor nonbinary elimination is used.
All operators, the central fixed layer and the original chosen seed are
retained. The next module applies this to the common-Q join from 11.1.2.

Earlier 7.0.1 and 3.2.5 remain explicit, with producers
qt-d-1222-normalized-nonff and qt-baumann-fsu. The final earlier-source
assembly belongs to qt-d-1222-natural-local-geometry. Common-normal
existence, the SL₃(4) row, the new point's placement and both orientations
remain with qt-d-1222-natural-relative-components.
Source: Aschbacher--Smith, 11.1.2, printed pp.763--764, applying
3.2.5, B.5.1 and 11.0.2, printed pp.580,99--103,759--760.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.QuasisimpleNormalizer
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
open Chapter12.Section02 ChapterB.QuasisimpleSource
open ShadowReduction.ComponentGeometry.Triangle.Reselection.Classification
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {I U : Subgroup G}

omit [Finite G] in
/-- The two simple field-four models give their actual order and simplicity,
without a relation to the original vertex. -/
theorem simple_four_model_data
    (hm : Source.IsSp (I ⧸ pCore 2 I) 2 4 ∨
      ClassificationModels.IsG2At (I ⧸ pCore 2 I) 4) :
    IsSimpleGroup (I ⧸ pCore 2 I) ∧ FieldFourOrder (Nat.card (I ⧸ pCore 2 I)) := by
  rcases hm with ⟨F,hF,hfin,hc,⟨e⟩⟩ | ⟨F,hF,hfin,hc,⟨e⟩⟩
  · let := hF
    let := hfin
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
      (by simpa [← Nat.card_eq_fintype_card] using hc)
    let := Theory.SpecificGroups.SymplecticFour.SimpleQuotients.isSimpleGroup
      (F := F) (by omega)
    let : IsSimpleGroup (Matrix.symplecticGroup (Fin 2) F) :=
      Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.isSimpleGroup
    refine ⟨e.isSimpleGroup, Or.inl ?_⟩
    rw [Nat.card_congr e.toEquiv, Theory.SpecificGroups.SymplecticFour.card_sp,hc]
    norm_num
  · let := hF
    let := hfin
    let := Atlas.G2.isSimple (K := F) (by omega)
    refine ⟨e.isSimpleGroup, Or.inr ?_⟩
    rw [Nat.card_congr e.toEquiv, Atlas.G2.card_Model,hc]
    norm_num

private theorem orbit_ff_of_simple_four (D : ChosenModule T I U)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T I)
    (hs : IsSimpleGroup (I ⧸ pCore 2 I))
    (hc : FieldFourOrder (Nat.card (I ⧸ pCore 2 I)))
    (h701 : Chapter7.NormalizedSource.Alternatives G D.orbitRepresentation D.orbitComponent) :
    IsFFModule D.sourceOrbitNormalizerRepresentation := by
  rcases h701 with hff | ⟨n,hn,⟨m⟩⟩ | hj
  · exact hff
  · let : NeZero n := ⟨by omega⟩
    let F : BinaryField := {
      Carrier := OrthogonalFourMinus.FiniteModel.Field n
      degree := 2*n
      degree_pos := by omega
      card_eq := GaloisField.card 2 (2*n) (by omega) }
    have he := (orbitComponentEquiv D h.toHypothesis1221 hs).trans m.groupEquiv
    exact (no_linearTwo_order F ((Nat.card_congr he.toEquiv) ▸ hc)).elim
  · exact (h.no_J4 hj).elim

private theorem moved_eq_of_component_equiv
    {P Q W : Type*} [Group P] [Group Q] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) P W) (τ : Representation (ZMod 2) Q W)
    {K : Subgroup P} {J : Subgroup Q} (e : K ≃* J)
    (he : ∀ k : K, τ (e k) = ρ k) : moved τ J = moved ρ K := by
  unfold moved subspaceCommutator
  congr 1
  ext v
  constructor
  · rintro ⟨j, hj, w, hw, rfl⟩
    obtain ⟨k, hk⟩ := e.surjective ⟨j, hj⟩
    refine ⟨k, k.property, w, hw, ?_⟩
    have ha := he k
    rw [hk] at ha
    rw [ha]
  · rintro ⟨k, hk, w, hw, rfl⟩
    refine ⟨e ⟨k, hk⟩, (e ⟨k, hk⟩).property, w, hw, ?_⟩
    rw [he]

private theorem not_doubled_of_simple_four_ff (D : ChosenModule T I U)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T I)
    (hsimple : IsSimpleGroup (I ⧸ pCore 2 I))
    (horder : FieldFourOrder (Nat.card (I ⧸ pCore 2 I)))
    (hff : IsFFModule D.sourceOrbitNormalizerRepresentation) : ¬ D.MarkedDoubled := by
  intro hd
  obtain ⟨A, _, hle, ⟨c⟩⟩ := D.doubledOrbit_full_normalizer_source h hd hff
  let σ := D.orbitRepresentation.comp D.orbitComponent.subtype
  have hf : Function.Injective σ :=
    (subspaceImageRepresentation_injective _ _).comp D.orbitComponent.subtype_injective
  let J := offenderSubgroup (linearAction (supplement σ A))
  let τ := (linearAction (supplement σ A)).comp J.subtype
  let C := (component σ A).subgroupOf J
  let e : D.orbitComponent ≃* C := supplementActorEquiv σ hf A J hle
  have he (k : D.orbitComponent) : τ (e k) = D.orbitRepresentation k :=
    supplementActorEquiv_action σ hf A J hle k
  have hc : FieldFourOrder (Nat.card C) :=
    (Nat.card_congr ((orbitComponentEquiv D h hsimple).trans e).toEquiv) ▸
      horder
  have hi : IsIrrPlus τ C c.sectionData.space.toSubmodule :=
    irrPlus_of_sourceCase τ hc c.clause_one
  have hm : moved τ C = ⊤ :=
    (moved_eq_of_component_equiv D.orbitRepresentation τ e he).trans (orbit_moved_eq_top D)
  have htop : IsIrrPlus τ C ⊤ := by
    have hs : c.sectionData.space.toSubmodule = ⊤ := c.sectionData.space_eq.trans hm
    simpa only [hs] using hi
  have hs : IsIrrPlus D.orbitRepresentation D.orbitComponent
      (D.space.comap D.orbitSpace.subtype) :=
    D.irrPlus.isIrrPlus.restricted (reducedRepresentation (I ⊔ (T : Subgroup G)))
      D.orbitSpace_component_invariant D.seed_le_orbitSpace
  have hs' : IsIrrPlus τ C (D.space.comap D.orbitSpace.subtype) := by
    apply hs.of_intertwining D.orbitRepresentation τ e.toMonoidHom e.surjective
      LinearMap.id (fun _ _ hh => hh)
    · intro k v
      exact LinearMap.congr_fun (he k) v
    · exact Submodule.map_id _
  have hsame := hs'.eq_of_le τ htop le_top
  have hspace : D.orbitSpace = D.space := by
    have hh := congrArg (Submodule.map D.orbitSpace.subtype) hsame
    rw [Submodule.map_comap_subtype, Submodule.map_top, Submodule.range_subtype,
      inf_eq_right.mpr D.seed_le_orbitSpace] at hh
    exact hh.symm
  have horbit : D.sourceOrbit = U := by
    change subspaceImage (I ⊔ (T : Subgroup G)) D.orbitSpace = U
    rw [hspace, D.image_eq]
  obtain ⟨t, ht, hnt, _⟩ := hd.2.2
  apply hnt
  rw [← horbit, D.sourceOrbit_eq]
  exact le_normalizer_componentOrbit U T ht

/-- The preceding source alternatives fix the same seed and force its
full linear normalizer to be FF in either simple field-four model. -/
theorem simple_four_seed_invariant_ff (D : ChosenModule T I U)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T I)
    (hm : Source.IsSp (I ⧸ pCore 2 I) 2 4 ∨
      ClassificationModels.IsG2At (I ⧸ pCore 2 I) 4)
    (h701 : Chapter7.NormalizedSource.Alternatives G D.orbitRepresentation D.orbitComponent)
    (h325 : D.Source325Alternatives) :
    (T : Subgroup G) ≤ normalizer (U : Set G) ∧
      IsFFModule (normalizerRepresentation D.chosenAction) := by
  obtain ⟨hs,hc⟩ := simple_four_model_data hm
  have hff := orbit_ff_of_simple_four D h hs hc h701
  have hd := not_doubled_of_simple_four_ff D h.toHypothesis1221 hs hc hff
  have he := orbit_eq_seed_of_source325 D h325 hd
  refine ⟨?_, seed_ff_of_orbit_eq D he hff⟩
  rw [← he, D.sourceOrbit_eq]
  exact le_normalizer_componentOrbit _ _

/-- Earlier B.5 recognition gives the actual natural marking on the same
central quotient, independently of either triangle orientation. -/
theorem simple_four_natural_of_source701325 (D : ChosenModule T I U)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T I)
    (hm : Source.IsSp (I ⧸ pCore 2 I) 2 4 ∨
      ClassificationModels.IsG2At (I ⧸ pCore 2 I) 4)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (h701 : Chapter7.NormalizedSource.Alternatives G D.orbitRepresentation D.orbitComponent)
    (h325 : D.Source325Alternatives) :
    ∃ S : D.NonbinaryNaturalInput, S.field.degree = 2 ∧
      ((Source.IsSp (I ⧸ pCore 2 I) 2 4 ∧ Nonempty
        (ActionEquiv D.centralQuotientAction (binarySymplectic S.field))) ∨
       (ClassificationModels.IsG2At (I ⧸ pCore 2 I) 4 ∧ Nonempty
        (ActionEquiv D.centralQuotientAction (binaryG2 S.field)))) := by
  obtain ⟨hs,hc⟩ := simple_four_model_data hm
  obtain ⟨hTU,hff⟩ := simple_four_seed_invariant_ff D h hm h701 h325
  obtain ⟨F,hF,hrow⟩ := fieldFourAction_of_ff D h.toHypothesis1221 hs hc hff
  rcases hrow with ⟨hc,ha⟩ | ⟨hc,ha⟩
  · have hsp : Source.IsSp (I ⧸ pCore 2 I) 2 4 := by
      obtain ⟨a⟩ := ha
      exact ⟨F.Carrier,inferInstance,inferInstance,by rw [F.card_eq,hF]; decide,⟨a.groupEquiv⟩⟩
    exact ⟨⟨h,hmany,hTU,hff,F,by omega,D.centralQuotientAction_injective hs,.sp4 ha⟩,
      hF,Or.inl ⟨hsp,ha⟩⟩
  · have hg2 : ClassificationModels.IsG2At (I ⧸ pCore 2 I) 4 := by
      obtain ⟨a⟩ := ha
      exact ⟨F.Carrier,inferInstance,inferInstance,by rw [F.card_eq,hF]; decide,⟨a.groupEquiv⟩⟩
    exact ⟨⟨h,hmany,hTU,hff,F,by omega,D.centralQuotientAction_injective hs,.g2 ha⟩,
      hF,Or.inr ⟨hg2,ha⟩⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
