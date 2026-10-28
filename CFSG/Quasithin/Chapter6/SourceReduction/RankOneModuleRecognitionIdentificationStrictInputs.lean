module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationStrictFixed
public import CFSG.Quasithin.ChapterG.Section09.Setup

/-!
# The literal G.10 and low-rank G.11 inputs in the strict branch

The same commutator form on U/Z(U), nonzero point of Z_S-hat, crossing
space E-hat, actor X-dot and smaller actor Z(U)^d-dot satisfy every
field of G.10.1. In particular the fixed bound uses the center preimage,
the numerical field uses the literal relative quotient, and transvections
retain their complete linear functionals.

The original Sylow image fixes the point and normalizes X-dot. The actual
layer involution belongs to X-dot, has type a₂ and moves precisely the
original plane. Its stabilizer is not transitive on that plane. The
original involution centralizer supplies the SQTK cover of the faithful
quotient, with no classification assumption.

Source: Aschbacher--Smith, 6.2.18 and G.11.1(3ii),(4), printed pp.690
and 364. This supplies local hypotheses, not G.11.2 or the strict
contradiction. Their assembly remains with
qt-d-1222-recognition-strict-elimination, using the classifier owned by
qt-g112-low-rank-symplectic-classification. LocalAnalysis is supplied by
qt-d-1222-rankone-recognition-identification.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

/-- The original Sylow image fixes the original marked binary point. -/
theorem LocalAnalysis.strict_sylow_fixes_point
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    [IsElementaryAbelian 2 (StrictVectorQuotient (T : Subgroup G) L R z)]
    {v : Additive (StrictVectorQuotient (T : Subgroup G) L R z)}
    (hv : v ∈ strictSourceLine (T : Subgroup G) L R z) :
    let q := QuotientGroup.mk' (strictQuotientAction (T : Subgroup G) L R z).ker
    let S := (T.subtype hTH).mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
    (S : Subgroup (StrictActor (T : Subgroup G) L R z)) ≤
      ChapterG.Section10.pointCentralizer (strictRepresentation (T : Subgroup G) L R z) v := by
  dsimp only
  rintro _ ⟨t, ht, rfl⟩
  exact A.strict_sourceLine_fixed_of_mem h611 hnatural hz horder hstrict t
    (h611.sylow_le ht) v hv

/-- Every field of the original G.10.1 hypothesis for the same commutator
form, source point, crossing space and relative smaller actor. -/
theorem LocalAnalysis.strict_g10_hypothesis
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    {d : G} (hdres : d ∈ strictCrossingResidual (T : Subgroup G) L R)
    (hdH : d ∉ centralizer ({z} : Set G))
    [IsElementaryAbelian 2 (StrictVectorQuotient (T : Subgroup G) L R z)]
    [IsElementaryAbelian 2 (strictCrossingImage (T : Subgroup G) L R z d)]
    (B : LinearMap.BilinForm (ZMod 2) (Additive (StrictVectorQuotient (T : Subgroup G) L R z)))
    (hBa : B.IsAlt) (hBn : B.Nondegenerate)
    (hpres : ∀ a x y, B (strictRepresentation (T : Subgroup G) L R z a x)
      (strictRepresentation (T : Subgroup G) L R z a y) = B x y)
    (hB : ∀ u v : sourceClosure (T : Subgroup G) L R z,
      B (strictHatElement (T : Subgroup G) L R z u)
        (strictHatElement (T : Subgroup G) L R z v) = 0 ↔ Commute u v)
    (v : Additive (StrictVectorQuotient (T : Subgroup G) L R z))
    (hv : v ∈ strictSourceLine (T : Subgroup G) L R z) (hv0 : v ≠ 0) :
    let X := strictCrossingImage (T : Subgroup G) L R z d
    ChapterG.Section10.Hypothesis (strictRepresentation (T : Subgroup G) L R z) B v
      (strictHatSpace (T : Subgroup G) L R z (strictCrossingIntersection (T : Subgroup G) L R z d))
      X ((strictCrossingCenterImage (T : Subgroup G) L R z d).subgroupOf X) := by
  let V := Additive (StrictVectorQuotient (T : Subgroup G) L R z)
  let E := strictHatSpace (T : Subgroup G) L R z (strictCrossingIntersection (T : Subgroup G) L R z d)
  let X := strictCrossingImage (T : Subgroup G) L R z d
  let X₀ := (strictCrossingCenterImage (T : Subgroup G) L R z d).subgroupOf X
  let ρ := strictRepresentation (T : Subgroup G) L R z
  have hdL : d ∈ L := (map_subtype_le _ hdres).1
  have hdZ : d ∈ normalizer (ZS (T : Subgroup G) L R : Set G) := (map_subtype_le _ hdres).2
  have hSE : strictSourceLine (T : Subgroup G) L R z ≤ E := by
    intro w hw
    change w.toMul ∈ ((strictCrossingIntersection (T : Subgroup G) L R z d).subgroupOf
      (sourceClosure (T : Subgroup G) L R z)).map _
    exact map_mono (comap_mono (strict_plane_le_crossing h611 hz hdZ)) hw
  have hvE : v ∈ E := hSE hv
  have hline : strictSourceLine (T : Subgroup G) L R z = Submodule.span (ZMod 2) {v} :=
    eq_span_singleton_of_mem_of_finrank_eq_one
      (A.strictSourceLine_finrank h611 hnatural hz horder hstrict) hv hv0
  have horth (u : V) : B v u = 0 ↔ u ∈ B.orthogonal (strictSourceLine (T : Subgroup G) L R z) := by
    constructor
    · intro hu w hw
      rw [hline] at hw
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
      simp only [map_smul, LinearMap.smul_apply, hu, smul_zero]
    · intro hu
      exact hu v hv
  obtain ⟨ht, hfull⟩ := A.strict_crossing_full_transvections h611 hnatural hz horder hTH hstrict
    hdL hdZ hdH ⟨v, hvE⟩ hv0 hv
  let q := QuotientGroup.mk' (strictQuotientAction (T : Subgroup G) L R z).ker
  let S := (T.subtype hTH).mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hSC := A.strict_sylow_fixes_point h611 hnatural hz horder hTH hstrict hv
  refine {
    faithful := strictRepresentation_injective _ _ _ _
    alternating := hBa
    nondegenerate := hBn
    preserves := hpres
    point_ne_zero := hv0
    point_mem := hvE
    isotropic := ?_
    fixes_point := fun _ ha => strict_crossingImage_fixes_sourceLine h611 hz d ha hv
    orbit_span := A.strictSourcePoint_orbit_span h611 hnatural hz horder hstrict v hv hv0
    odd_index := ?_
    dimension := ?_
    displacement := ?_
    fixed_bound := ?_
    transvections := ht
    full_transvections := hfull }
  · let := A.strict_crossing_elementary h611 hnatural hz horder hstrict hdH
    exact strict_hat_isotropic_of_commutative B hB _
  · exact Nat.not_even_iff_odd.mp (fun he => S.not_dvd_index
      ((even_iff_two_dvd.mp he).trans (index_dvd_of_le hSC)))
  · have hr := A.strict_crossing_quotient_rank h611 hnatural hz horder hTH hstrict hdres hdH
    change Module.finrank (ZMod 2) E + Group.rank (X ⧸ X₀) + 1 = Module.finrank (ZMod 2) V at hr
    change Module.finrank (ZMod 2) E + Group.rank (X ⧸ X₀) = Module.finrank (ZMod 2) V - 1
    omega
  · intro a u hu
    exact strict_crossing_perpendicular_displacement h611 hz hstrict B hB hdZ a.property ((horth u).mp hu)
  · intro a ha u hfix
    apply (horth u).mpr
    rw [← strict_centralizer_hat_eq_orthogonal B hB (hstrict.le.trans inf_le_left)]
    exact A.strict_crossing_fixed_bound h611 hnatural hz horder hTH hstrict hdres hdH a.property ha hfix

/-- The actual faithful quotient is a quotient of the original SQTK
involution centralizer; no classifier is assumed. -/
def strictSQTKCover
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (horder : orderOf z = 2) :
    ChapterG.Section09.SQTKCover KnownSimple.IsKnownSimple (StrictActor (T : Subgroup G) L R z) where
  Cover := centralizer ({z} : Set G)
  sqtk := h611.simpleQTKE.involution_centralizer_sqtk horder
  projection := QuotientGroup.mk' (strictQuotientAction (T : Subgroup G) L R z).ker
  surjective := QuotientGroup.mk'_surjective _


/-- All local inputs to G.11.1(3ii), on the original quotient action.
The classification and elimination of its alternatives remain separate. -/
theorem LocalAnalysis.strict_g11_inputs
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    {d : G} (hdres : d ∈ strictCrossingResidual (T : Subgroup G) L R)
    (hdH : d ∉ centralizer ({z} : Set G))
    (hdS : d ∈ normalizer ((T : Subgroup G) ⊓ L : Set G)) (hd3 : orderOf d = 3) :
    ∃ he : IsElementaryAbelian 2 (StrictVectorQuotient (T : Subgroup G) L R z),
      letI := he
      ∃ hX : IsElementaryAbelian 2 (strictCrossingImage (T : Subgroup G) L R z d),
        letI := hX
        ∃ (B : LinearMap.BilinForm (ZMod 2) (Additive (StrictVectorQuotient (T : Subgroup G) L R z)))
          (v : Additive (StrictVectorQuotient (T : Subgroup G) L R z)),
          let ρ := strictRepresentation (T : Subgroup G) L R z
          let X := strictCrossingImage (T : Subgroup G) L R z d
          let X₀ := (strictCrossingCenterImage (T : Subgroup G) L R z d).subgroupOf X
          let q := QuotientGroup.mk' (strictQuotientAction (T : Subgroup G) L R z).ker
          let S := (T.subtype hTH).mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
          ChapterG.Section10.Hypothesis ρ B v
            (strictHatSpace (T : Subgroup G) L R z (strictCrossingIntersection (T : Subgroup G) L R z d)) X X₀ ∧
          v ∈ strictSourceLine (T : Subgroup G) L R z ∧
          (∀ u w : sourceClosure (T : Subgroup G) L R z,
            B (strictHatElement (T : Subgroup G) L R z u)
              (strictHatElement (T : Subgroup G) L R z w) = 0 ↔ Commute u w) ∧
          4 ≤ Module.finrank (ZMod 2) (Additive (StrictVectorQuotient (T : Subgroup G) L R z)) ∧
          Nonempty (ChapterG.Section09.SQTKCover KnownSimple.IsKnownSimple (StrictActor (T : Subgroup G) L R z)) ∧
          (S : Subgroup (StrictActor (T : Subgroup G) L R z)) ≤ ChapterG.Section10.pointCentralizer ρ v ∧
          X ≤ (S : Subgroup (StrictActor (T : Subgroup G) L R z)) ∧
          (X.subgroupOf (S : Subgroup (StrictActor (T : Subgroup G) L R z))).Normal ∧
          ∃ a ∈ X, a ≠ 1 ∧ a ^ 2 = 1 ∧
            Representation.RankTwo.movedSpace ρ a = strictCentralPlane (T : Subgroup G) L R z ∧
            Module.finrank (ZMod 2) (Representation.RankTwo.movedSpace ρ a) = 2 ∧
            v ∈ Representation.RankTwo.movedSpace ρ a ∧
            (∀ w, B w (ρ a w) = 0) ∧
            ¬ Representation.RankTwo.StabilizerTransitive ρ (Representation.RankTwo.movedSpace ρ a) := by
  have hdZ : d ∈ normalizer (ZS (T : Subgroup G) L R : Set G) := (map_subtype_le _ hdres).2
  obtain ⟨he, B, ha, hn, hdim, hpres, hB, _⟩ :=
    A.strict_crossing_symplectic_geometry h611 hnatural hz horder hstrict hdZ hdH
  let := he
  let hX := A.strict_crossingImage_elementary h611 hnatural hz horder hstrict hdZ
  let := hX
  have hline := A.strictSourceLine_finrank h611 hnatural hz horder hstrict
  have hne : strictSourceLine (T : Subgroup G) L R z ≠ ⊥ := by
    intro heq
    rw [heq, finrank_bot] at hline
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨hXS, hnormal⟩ := A.strict_crossing_normal_in_sylow h611 hnatural hz horder hTH hstrict hdZ
  refine ⟨he, hX, B, v,
    A.strict_g10_hypothesis h611 hnatural hz horder hTH hstrict hdres hdH B ha hn hpres hB v hv hv0,
    hv, hB, hdim, ⟨strictSQTKCover h611 horder⟩,
    A.strict_sylow_fixes_point h611 hnatural hz horder hTH hstrict hv, hXS, hnormal, ?_⟩
  obtain ⟨a, ha1, _⟩ := (Nat.card_eq_two_iff' (1 : strictLayerImage (T : Subgroup G) L R z)).mp
    (A.strict_layer_actor_image_card h611 hnatural hz horder hstrict)
  have hane : (a : StrictActor (T : Subgroup G) L R z) ≠ 1 := fun hh => ha1 (Subtype.ext hh)
  obtain ⟨_, _, _, _, _, _, hact⟩ := A.strict_symplectic_layer_action h611 hnatural hz horder hstrict
  obtain ⟨ha2, hmoved, hr, _⟩ := hact a a.property hane
  refine ⟨a, A.strict_layerImage_le_crossingImage h611 hnatural hz horder hstrict
      (map_subtype_le _ hdres).1 hdS hd3 a.property,
    hane, ha2, hmoved, hr, ?_, A.strict_layer_form_zero h611 hnatural hz horder hstrict B hB a.property, ?_⟩
  · rw [hmoved]
    exact strictSourceLine_le_plane hstrict hv
  · rw [hmoved]
    exact A.strict_plane_not_stabilizerTransitive h611 hnatural hz horder hstrict

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
