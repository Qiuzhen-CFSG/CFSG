module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationStrictAction
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationStrictCrossingNormality
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationStrictCrossingSymplectic

/-!
# The crossed configuration on the whole reduced Chapter 12 layer

The strict branch constructs a cubic in O²(N_L(Z_S)), its elementary
crossed intersection, and the actual dotted actors X and Z(U)^d. Their
images are normal in the marked stabilizer, and X is normal in the
image of the original Sylow subgroup. The same commutator form makes
E-hat isotropic and identifies C_U(Z_S)-hat with the source-line
perpendicular hyperplane.

The original layer provides an a₂ involution inside X, with moved plane
containing the marked nonzero source vector. That vector is fixed by X
and the Sylow image and has spanning orbit. The moved-plane stabilizer
is not transitive. Thus this application supplies the G.11 low-rank and
Sylow-normality inputs from the whole reduced layer without any new
local premise beyond LocalAnalysis.

Source: Aschbacher--Smith, 6.2.17--18, G.11.1(3ii),(4) and 12.2.2(3d).
The remaining G.10 fixed-space, transvection and rank inputs and the
strict contradiction stay with qt-d-1222-recognition-strict-elimination.
LocalAnalysis is discharged by qt-d-1222-rankone-recognition-identification.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Chapter6.Source Chapter6.Source.RankOneRecognition
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L : Subgroup G} {n : ℕ} {z : G}

/-- The whole reduced layer supplies the actual crossing group and source
G.11 low-rank and Sylow-normality conditions, with no added local callback. -/
theorem strict_reduced_crossing_configuration
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (A : LocalAnalysis (T : Subgroup G) L (normalizer (L : Set G)) (wholeReduced T L) z)
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hstrict : ZS (T : Subgroup G) L (wholeReduced T L) <
      sourceClosure (T : Subgroup G) L (wholeReduced T L) z ⊓ commutatorLayer T L) :
    ∃ d ∈ strictCrossingResidual (T : Subgroup G) L (wholeReduced T L),
      d ∈ L ∧ orderOf d = 3 ∧ d ∉ centralizer ({z} : Set G) ∧
      IsElementaryAbelian 2 (strictCrossingIntersection (T : Subgroup G) L (wholeReduced T L) z d) ∧
      IsElementaryAbelian 2 (strictCrossingImage (T : Subgroup G) L (wholeReduced T L) z d) ∧
      ∃ he : IsElementaryAbelian 2 (StrictVectorQuotient (T : Subgroup G) L (wholeReduced T L) z),
        letI := he
        let ρ := strictRepresentation (T : Subgroup G) L (wholeReduced T L) z
        let E := strictHatSpace (T : Subgroup G) L (wholeReduced T L) z
          (strictCrossingIntersection (T : Subgroup G) L (wholeReduced T L) z d)
        let X := strictCrossingImage (T : Subgroup G) L (wholeReduced T L) z d
        let X₀ := strictCrossingCenterImage (T : Subgroup G) L (wholeReduced T L) z d
        let q := QuotientGroup.mk' (strictQuotientAction (T : Subgroup G) L (wholeReduced T L) z).ker
        let S := (T.subtype hTH).mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
        ∃ B : LinearMap.BilinForm (ZMod 2)
            (Additive (StrictVectorQuotient (T : Subgroup G) L (wholeReduced T L) z)),
          B.IsAlt ∧ B.Nondegenerate ∧
          4 ≤ Module.finrank (ZMod 2) (Additive (StrictVectorQuotient (T : Subgroup G) L (wholeReduced T L) z)) ∧
          Function.Injective ρ ∧
          (∀ g v w, B (ρ g v) (ρ g w) = B v w) ∧
          (∀ v ∈ E, ∀ w ∈ E, B v w = 0) ∧
          strictHatSpace (T : Subgroup G) L (wholeReduced T L) z
            (sourceClosure (T : Subgroup G) L (wholeReduced T L) z ⊓
              centralizer (ZS (T : Subgroup G) L (wholeReduced T L) : Set G)) =
            B.orthogonal (strictSourceLine (T : Subgroup G) L (wholeReduced T L) z) ∧
          Module.finrank (ZMod 2) (B.orthogonal (strictSourceLine (T : Subgroup G) L (wholeReduced T L) z)) + 1 =
            Module.finrank (ZMod 2) (Additive (StrictVectorQuotient (T : Subgroup G) L (wholeReduced T L) z)) ∧
          X₀ ≤ X ∧ (X₀.subgroupOf X).Normal ∧
          X ≤ (S : Subgroup (StrictActor (T : Subgroup G) L (wholeReduced T L) z)) ∧
          (X.subgroupOf (S : Subgroup (StrictActor (T : Subgroup G) L (wholeReduced T L) z))).Normal ∧
          ∃ a ∈ X, a ≠ 1 ∧ a ^ 2 = 1 ∧
            Representation.RankTwo.movedSpace ρ a = strictCentralPlane (T : Subgroup G) L (wholeReduced T L) z ∧
            Module.finrank (ZMod 2) (Representation.RankTwo.movedSpace ρ a) = 2 ∧
            (∀ w, B w (ρ a w) = 0) ∧
            ¬ Representation.RankTwo.StabilizerTransitive ρ (Representation.RankTwo.movedSpace ρ a) ∧
            ∃ v : Additive (StrictVectorQuotient (T : Subgroup G) L (wholeReduced T L) z),
              v ≠ 0 ∧ v ∈ E ∧ v ∈ Representation.RankTwo.movedSpace ρ a ∧
              Submodule.span (ZMod 2) {w | ∃ g, ρ g v = w} = ⊤ ∧
              (∀ x ∈ X, ρ x v = v) ∧
              ∀ s ∈ (S : Subgroup (StrictActor (T : Subgroup G) L (wholeReduced T L) z)), ρ s v = v := by
  obtain ⟨d, hdres, hdL, hdS, hdZ, hd, hdH⟩ := strict_exists_crossing_cubic h611 hnatural hz horder
  obtain ⟨he, B, hBa, hBn, hdim, hinv, hcomm, hperp, hcodim, hlineE, hE⟩ :=
    A.strict_crossing_symplectic_geometry h611 hnatural hz horder hstrict hdZ hdH
  let := he
  let ρ := strictRepresentation (T : Subgroup G) L (wholeReduced T L) z
  let X := strictCrossingImage (T : Subgroup G) L (wholeReduced T L) z d
  let X₀ := strictCrossingCenterImage (T : Subgroup G) L (wholeReduced T L) z d
  let C := centralizer (strictLayerImage (T : Subgroup G) L (wholeReduced T L) z : Set (StrictActor (T : Subgroup G) L (wholeReduced T L) z))
  let q := QuotientGroup.mk' (strictQuotientAction (T : Subgroup G) L (wholeReduced T L) z).ker
  let S := (T.subtype hTH).mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  obtain ⟨hXC, _, hZX, hZn⟩ := A.strict_crossing_normal_in_layer_centralizer h611 hnatural hz horder hstrict hdZ
  have hZnormal : (X₀.subgroupOf X).Normal :=
    (normal_subgroupOf_iff_le_normalizer hZX).mpr
      (hXC.trans ((normal_subgroupOf_iff_le_normalizer (hZX.trans hXC)).mp hZn))
  obtain ⟨hXS, hXn⟩ := A.strict_crossing_normal_in_sylow h611 hnatural hz horder hTH hstrict hdZ
  refine ⟨d, hdres, hdL, hd, hdH,
    A.strict_crossing_elementary h611 hnatural hz horder hstrict hdH,
    A.strict_crossingImage_elementary h611 hnatural hz horder hstrict hdZ,
    he, B, hBa, hBn, hdim, strictRepresentation_injective _ _ _ _, hinv, hE, hperp, hcodim,
    hZX, hZnormal, hXS, hXn, ?_⟩
  have hcard : Nat.card (strictLayerImage (T : Subgroup G) L (wholeReduced T L) z) = 2 :=
    A.strict_layer_actor_image_card h611 hnatural hz horder hstrict
  have hne : strictLayerImage (T : Subgroup G) L (wholeReduced T L) z ≠ ⊥ := by
    intro hh
    rw [hh, card_bot] at hcard
    contradiction
  obtain ⟨a, ha⟩ := ne_bot_iff_exists_ne_one.mp hne
  have ha0 : (a : StrictActor (T : Subgroup G) L (wholeReduced T L) z) ≠ 1 :=
    fun hh => ha (Subtype.ext hh)
  obtain ⟨he', B', _, _, _, _, hmark⟩ :=
    A.strict_symplectic_layer_action h611 hnatural hz horder hstrict
  obtain ⟨ha2, hmove, hrank, _⟩ := hmark a a.property ha0
  refine ⟨a, A.strict_layerImage_le_crossingImage h611 hnatural hz horder hstrict hdL hdS hd a.property,
    ha0, ha2, hmove, hrank,
    A.strict_layer_form_zero h611 hnatural hz horder hstrict B hcomm a.property, ?_, ?_⟩
  · rw [hmove]
    exact A.strict_plane_not_stabilizerTransitive h611 hnatural hz horder hstrict
  · have hdimL := A.strictSourceLine_finrank h611 hnatural hz horder hstrict
    have hneL : strictSourceLine (T : Subgroup G) L (wholeReduced T L) z ≠ ⊥ := by
      intro hh
      rw [hh, finrank_bot] at hdimL
      contradiction
    obtain ⟨v, hv, hv0⟩ := (strictSourceLine (T : Subgroup G) L (wholeReduced T L) z).ne_bot_iff.mp hneL
    refine ⟨v, hv0, hlineE hv, ?_,
      A.strictSourcePoint_orbit_span h611 hnatural hz horder hstrict v hv hv0, ?_, ?_⟩
    · rw [hmove]
      exact strictSourceLine_le_plane hstrict hv
    · exact fun x hx => strict_crossingImage_fixes_sourceLine h611 hz d hx hv
    · rintro s ⟨t, ht, rfl⟩
      exact A.strict_sourceLine_fixed_of_mem h611 hnatural hz horder hstrict t (h611.sylow_le ht) v hv

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
