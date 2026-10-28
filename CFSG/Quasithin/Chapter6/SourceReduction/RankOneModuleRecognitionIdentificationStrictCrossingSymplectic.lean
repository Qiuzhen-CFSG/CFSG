module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationStrictCrossing
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Crossing spaces for the actual commutator form

Orthogonality in U/Z(U) is proved equivalent to commutation of the
original representatives. Consequently C_U(Z_S) has image Z_S-hat-perp,
a hyperplane. The elementary crossed intersection E has totally
isotropic image containing the marked source line. The layer retains
its type-a₂ equation for this same form.

The form, its nondegeneracy and invariance are constructed from the
actual Frattini commutator. No arbitrary orthogonality identification
or extra module action is assumed in the source theorem.

Source: Aschbacher--Smith, 6.2.17(3)--(4), printed pp.689--690.
The remaining fixed-space, full-transvection and rank calculations
stay with qt-d-1222-recognition-strict-elimination. LocalAnalysis is
discharged by qt-d-1222-rankone-recognition-identification.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] {T L R : Subgroup G} {z : G}

@[expose] def strictHatSpace (T L R : Subgroup G) (z : G)
    [IsElementaryAbelian 2 (StrictVectorQuotient T L R z)] (D : Subgroup G) :
    Submodule (ZMod 2) (Additive (StrictVectorQuotient T L R z)) :=
  AddSubgroup.toZModSubmodule 2
    ((D.subgroupOf (sourceClosure T L R z)).map
      (QuotientGroup.mk' (center (sourceClosure T L R z)))).toAddSubgroup

@[expose] def strictHatElement (T L R : Subgroup G) (z : G)
    (u : sourceClosure T L R z) : Additive (StrictVectorQuotient T L R z) :=
  Additive.ofMul (QuotientGroup.mk' (center (sourceClosure T L R z)) u)

section Form
variable [IsElementaryAbelian 2 (StrictVectorQuotient T L R z)]
  (B : LinearMap.BilinForm (ZMod 2) (Additive (StrictVectorQuotient T L R z)))
  (hB : ∀ u v : sourceClosure T L R z,
    B (strictHatElement T L R z u) (strictHatElement T L R z v) = 0 ↔ Commute u v)

include hB

/-- Orthogonality for the actual commutator form is the ambient centralizer. -/
theorem strict_hat_orthogonal_iff (D : Subgroup G) (hD : D ≤ sourceClosure T L R z)
    (u : sourceClosure T L R z) :
    strictHatElement T L R z u ∈ B.orthogonal (strictHatSpace T L R z D) ↔
      (u : G) ∈ centralizer (D : Set G) := by
  constructor
  · intro hu d hd
    have hm : strictHatElement T L R z ⟨d, hD hd⟩ ∈ strictHatSpace T L R z D :=
      ⟨_, hd, rfl⟩
    exact congrArg Subtype.val ((hB ⟨d, hD hd⟩ u).mp (hu _ hm)).eq
  · intro hu v hv
    obtain ⟨d, hd, he⟩ := hv
    have he' : v = strictHatElement T L R z d := (congrArg Additive.ofMul he).symm
    rw [he']
    exact (hB d u).mpr (Subtype.ext (hu d hd))

/-- The image of C_U(Z_S) is exactly the perpendicular hyperplane. -/
theorem strict_centralizer_hat_eq_orthogonal (hSU : ZS T L R ≤ sourceClosure T L R z) :
    strictHatSpace T L R z (sourceClosure T L R z ⊓ centralizer (ZS T L R : Set G)) =
      B.orthogonal (strictSourceLine T L R z) := by
  ext v
  obtain ⟨u, he⟩ := QuotientGroup.mk'_surjective (center (sourceClosure T L R z)) v.toMul
  have he' : v = strictHatElement T L R z u := (congrArg Additive.ofMul he).symm
  rw [he']
  change strictHatElement T L R z u ∈ strictHatSpace T L R z _ ↔
    strictHatElement T L R z u ∈ B.orthogonal (strictHatSpace T L R z (ZS T L R))
  rw [strict_hat_orthogonal_iff B hB _ hSU]
  constructor
  · rintro ⟨w, hw, hew⟩
    have hm := (strict_hat_orthogonal_iff B hB _ hSU w).mpr hw.2
    have heq : strictHatElement T L R z w = strictHatElement T L R z u :=
      congrArg Additive.ofMul hew
    rw [heq] at hm
    exact (strict_hat_orthogonal_iff B hB _ hSU u).mp hm
  · intro hu
    exact ⟨u, ⟨u.property, hu⟩, rfl⟩

/-- Abelian ambient intersections have isotropic image for this precise form. -/
theorem strict_hat_isotropic_of_commutative (D : Subgroup G) [IsMulCommutative D] :
    ∀ v ∈ strictHatSpace T L R z D, ∀ w ∈ strictHatSpace T L R z D, B v w = 0 := by
  intro v hv w hw
  obtain ⟨a, ha, he⟩ := hv
  obtain ⟨b, hb, hf⟩ := hw
  have hc : Commute a b := by
    change a * b = b * a
    apply Subtype.ext
    exact congrArg (fun x : D => (x : G)) (mul_comm (⟨(a : G), ha⟩ : D) ⟨(b : G), hb⟩)
  simpa only [strictHatElement, he, hf, ofMul_toMul] using (hB a b).mpr hc

end Form

variable [Finite G] {κ : GroupClass} {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

/-- Source 6.2.17(3),(4) on the actual commutator symplectic quotient.
The orthogonal hyperplane has codimension one and the crossed intersection
has totally isotropic image containing the original source line. -/
theorem LocalAnalysis.strict_crossing_symplectic_geometry
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    {d : G} (hdZ : d ∈ normalizer (ZS (T : Subgroup G) L R : Set G))
    (hd : d ∉ centralizer ({z} : Set G)) :
    ∃ he : IsElementaryAbelian 2 (StrictVectorQuotient (T : Subgroup G) L R z),
      letI := he
      ∃ B : LinearMap.BilinForm (ZMod 2) (Additive (StrictVectorQuotient (T : Subgroup G) L R z)),
        B.IsAlt ∧ B.Nondegenerate ∧
        4 ≤ Module.finrank (ZMod 2) (Additive (StrictVectorQuotient (T : Subgroup G) L R z)) ∧
        (∀ a x y, B (strictRepresentation (T : Subgroup G) L R z a x)
          (strictRepresentation (T : Subgroup G) L R z a y) = B x y) ∧
        (∀ u v : sourceClosure (T : Subgroup G) L R z,
          B (strictHatElement (T : Subgroup G) L R z u)
            (strictHatElement (T : Subgroup G) L R z v) = 0 ↔ Commute u v) ∧
        strictHatSpace (T : Subgroup G) L R z
          (sourceClosure (T : Subgroup G) L R z ⊓ centralizer (ZS (T : Subgroup G) L R : Set G)) =
          B.orthogonal (strictSourceLine (T : Subgroup G) L R z) ∧
        Module.finrank (ZMod 2) (B.orthogonal (strictSourceLine (T : Subgroup G) L R z)) + 1 =
          Module.finrank (ZMod 2) (Additive (StrictVectorQuotient (T : Subgroup G) L R z)) ∧
        strictSourceLine (T : Subgroup G) L R z ≤
          strictHatSpace (T : Subgroup G) L R z (strictCrossingIntersection (T : Subgroup G) L R z d) ∧
        ∀ v ∈ strictHatSpace (T : Subgroup G) L R z (strictCrossingIntersection (T : Subgroup G) L R z d),
          ∀ w ∈ strictHatSpace (T : Subgroup G) L R z (strictCrossingIntersection (T : Subgroup G) L R z d),
            B v w = 0 := by
  obtain ⟨he, e, B, hBa, hBn, hdim, hcomm, hinv⟩ :=
    A.strict_symplectic_geometry h611 hnatural hz horder hstrict
  let := he
  have hB : ∀ u v : sourceClosure (T : Subgroup G) L R z,
      B (strictHatElement (T : Subgroup G) L R z u)
        (strictHatElement (T : Subgroup G) L R z v) = 0 ↔ Commute u v := by
    intro u v
    obtain ⟨c, hc, hb⟩ := hcomm u v
    rw [show B (strictHatElement (T : Subgroup G) L R z u)
      (strictHatElement (T : Subgroup G) L R z v) = (e c).toAdd from hb]
    constructor
    · intro hh
      have hec : e c = 1 := hh
      have hc1 : c = 1 := e.injective (hec.trans (map_one e).symm)
      apply commutatorElement_eq_one_iff_commute.mp
      rw [← hc, hc1]
      rfl
    · intro hh
      have hc1 : c = 1 := Subtype.ext (hc.trans (commutatorElement_eq_one_iff_commute.mpr hh))
      rw [hc1, map_one]
      rfl
  refine ⟨he, B, hBa, hBn, hdim, ?_, hB,
    strict_centralizer_hat_eq_orthogonal B hB (hstrict.le.trans inf_le_left), ?_, ?_, ?_⟩
  · intro a x y
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (strictQuotientAction (T : Subgroup G) L R z).ker a
    exact hinv (strictClosureAction (T : Subgroup G) L R z h) x.toMul y.toMul
  · rw [B.finrank_orthogonal hBn, A.strictSourceLine_finrank h611 hnatural hz horder hstrict]
    change _ + 1 = Module.finrank (ZMod 2) (Additive (sourceClosure (T : Subgroup G) L R z ⧸ center (sourceClosure (T : Subgroup G) L R z)))
    omega
  · intro v hv
    change v.toMul ∈ ((strictCrossingIntersection (T : Subgroup G) L R z d).subgroupOf (sourceClosure (T : Subgroup G) L R z)).map _
    exact map_mono (comap_mono (strict_plane_le_crossing h611 hz hdZ)) hv
  · let := A.strict_crossing_elementary h611 hnatural hz horder hstrict hd
    exact strict_hat_isotropic_of_commutative B hB _


/-- The original layer has type a₂ for this same commutator form. -/
theorem LocalAnalysis.strict_layer_form_zero
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    [IsElementaryAbelian 2 (StrictVectorQuotient (T : Subgroup G) L R z)]
    (B : LinearMap.BilinForm (ZMod 2) (Additive (StrictVectorQuotient (T : Subgroup G) L R z)))
    (hB : ∀ u v : sourceClosure (T : Subgroup G) L R z,
      B (strictHatElement (T : Subgroup G) L R z u)
        (strictHatElement (T : Subgroup G) L R z v) = 0 ↔ Commute u v)
    {a : StrictActor (T : Subgroup G) L R z}
    (ha : a ∈ strictLayerImage (T : Subgroup G) L R z) :
    ∀ x, B x (strictRepresentation (T : Subgroup G) L R z a x) = 0 := by
  obtain ⟨v, hv, rfl⟩ := ha
  intro x
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective
    (center (sourceClosure (T : Subgroup G) L R z)) x.toMul
  have hx : x = strictHatElement (T : Subgroup G) L R z u :=
    (congrArg Additive.ofMul hu).symm
  rw [hx]
  change B (strictHatElement (T : Subgroup G) L R z u)
    (Additive.ofMul (strictQuotientAction (T : Subgroup G) L R z v (QuotientGroup.mk' _ u))) = 0
  rw [strictQuotientAction_mk]
  exact (hB u _).mpr (A.strict_layer_commutes_conjugate h611 hnatural hz horder hstrict v hv u)

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
