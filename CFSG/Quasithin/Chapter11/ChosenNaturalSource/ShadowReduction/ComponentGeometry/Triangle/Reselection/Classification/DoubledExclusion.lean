module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Classification.SeedReduction
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Classification.Supplement
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.DoubledOrbitOffenders

/-!
# Excluding doubled seeds for the two field-four triangle components

The complete B.5.1 theorem applies to the actual doubled orbit, using its
two distinct constituents to kill the offender supplement's two-core.
The component orders exclude every repeated row, leaving an Irr⁺ orbit.
The original seed is also Irr⁺; the antichain property forces it to be
the whole orbit, contradicting the marked moving conjugator.

This local order argument does not require the stronger ambient H.9
normalizer identification. It feeds the swapped-module recognition in
11.4.1(2), whose final assembly remains with this triangle owner.
Source: Aschbacher--Smith B.5.1, 3.2.5 and 11.4.1, pp.99--103,580,776.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.QuasisimpleNormalizer
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Classification
open Chapter12.Section02 ChapterB.QuasisimpleSource LocalGeometry.Components

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

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L I U : Subgroup G}

omit [Finite G] in
theorem orbit_moved_eq_top (D : ChosenModule T I U) :
    moved D.orbitRepresentation D.orbitComponent = ⊤ := by
  let H := I ⊔ (T : Subgroup G)
  let X := I.subgroupOf H
  let : X.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le I.le_normalizer D.sylow_normalizes_component)
  exact restricted_commutator_eq_top (reducedRepresentation H) D.orbitSpace X
    D.orbitSpace_component_invariant
    (orbitSpan_full_commutator (reducedRepresentation H)
      (show (⊤ : Subgroup H) ≤ normalizer (X : Set H) from le_normalizer_of_normal)
      D.irrPlus.isIrrPlus)

/-- B.5.1 on the actual doubled orbit leaves only an Irr⁺ row. Its original
seed is also Irr⁺, so the antichain property forces the orbit to equal the
seed, contradicting the marked moving conjugator. -/
theorem not_doubled_of_orbit_ff (D : ChosenModule T I U)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T I)
    (ho : TriangleOrientation L I)
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
    (Nat.card_congr ((orbitComponentEquiv D h (orientation_simple ho)).trans e).toEquiv) ▸
      orientation_order ho
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

/-- The two genuine earlier source conclusions now fix the original seed
and make its full linear normalizer FF in either triangle orientation. -/
theorem seed_invariant_ff_of_source701325 (D : ChosenModule T I U)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T I)
    (ho : TriangleOrientation L I)
    (h701 : Chapter7.NormalizedSource.Alternatives G D.orbitRepresentation D.orbitComponent)
    (h325 : D.Source325Alternatives) :
    (T : Subgroup G) ≤ normalizer (U : Set G) ∧
      IsFFModule (normalizerRepresentation D.chosenAction) :=
  seed_invariant_ff_of_sources D h ho h701 h325
    (not_doubled_of_orbit_ff D h.toHypothesis1221 ho (orbit_ff_of_source701 D h ho h701))

/-- Apply the seed reduction to the actual third vertex and chosen module
of the original triangle. The parent component assembly owns the preceding
7.0.1 and 3.2.5 conclusions; no local doubled-exclusion callback remains. -/
theorem exists_triangle_seed_ff {V : Subgroup G} (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (K X : Subgroup G)
    (htriangle : FieldFourTriangle T L (f.Li 0) (f.Li 1) K X)
    (hKnormal : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K) :
    ∃ K₀ : Subgroup G, K₀ ∈ Chapter1.L G T ∧ K₀ ≤ K ∧ K₀ ≠ K ∧ K₀ ≠ f.Li 0 ∧
      TriangleOrientation L (K₀ ⊔ f.Li 1) ∧
      Hypothesis1223 KnownSimple.IsKnownSimple T (K₀ ⊔ f.Li 1) ∧
      ∃ (U : Subgroup G) (D_I : ChosenModule T (K₀ ⊔ f.Li 1) U),
        Chapter7.NormalizedSource.Alternatives G D_I.orbitRepresentation D_I.orbitComponent →
        D_I.Source325Alternatives →
        (T : Subgroup G) ≤ normalizer (U : Set G) ∧
          IsFFModule (normalizerRepresentation D_I.chosenAction) := by
  obtain ⟨K₀, hK, hle, hne, hne₁, ho, hI, U, ⟨D_I⟩⟩ :=
    exists_triangle_choice D S f K X htriangle hKnormal
  exact ⟨K₀, hK, hle, hne, hne₁, ho, hI, U, D_I,
    seed_invariant_ff_of_source701325 D_I hI ho⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Classification
