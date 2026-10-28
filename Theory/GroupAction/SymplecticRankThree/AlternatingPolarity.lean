module
public import Theory.GroupAction.SymplecticRankThree.CoordinateHyperplanes
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification.NonbinaryPolar.Collineation

/-!
# Alternating-form realization of the source null polarity

A semilinear lift T of a null correlation satisfies B(Tv,v)=0. Expanding
at v+w and cv+w forces the field automorphism to fix c, using one nonzero
cross pairing. Thus the lift is linear and defines a nondegenerate alternating
form. A symplectic basis puts this form in the standard matrix form.

Applying this to the polarity constructed from the source blocks converts
ordinary projective line coordinates into polar coordinates. The coordinate
construction itself is still a separate obligation. The nonbinary restriction
comes only from the existing fundamental theorem for collineations; the binary
source recognition is already proved in `BinaryHigman`.

Source: Higman (1964), Theorem 2(i), p.154, the null-polarity step following
Lemma 10. The scalar calculation below proves the alternating realization
rather than assuming a pairing formula or an equivariant model map.
-/

public noncomputable section
open Projectivization Module
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification

namespace Theory.GroupAction.SymplecticRankThree
variable {F : Type*} [Field F]

/-- A semilinear null correlation has trivial field automorphism. -/
theorem null_semilinear_field_eq_id (σ : F ≃+* F) (A : Vector F ≃ₗ[F] Vector F)
    (hn : ∀ v : Vector F, form F (A (fieldVector σ v)) v = 0) :
    σ = RingEquiv.refl F := by
  let T := A.toLinearMap.comp (fieldVector σ)
  have hT (v : Vector F) : T v = A (fieldVector σ v) := rfl
  have hc (v w : Vector F) : form F (T v) w + form F (T w) v = 0 := by
    have hh := hn (v+w)
    simpa only [map_add,LinearMap.add_apply,hn,zero_add,add_zero,hT,add_comm] using hh
  have hu : T (e 0) ≠ 0 := by
    change A (fieldVector σ (e 0)) ≠ 0
    exact (map_ne_zero_iff A A.injective).mpr (fieldVector_ne_zero σ (e 0) (by simp [Theory.SpecificGroups.SymplecticFour.e]))
  obtain ⟨w,hw⟩ : ∃ w, form F (T (e 0)) w ≠ 0 := by
    by_contra! hh
    exact hu (TwoLocalCover.form_nondegenerate.1 _ hh)
  have hs (c : F) : σ c = c := by
    have h₁ := hc (e 0) w
    have h₂ := hc (c • e 0) w
    have ht : T (c • e 0) = σ c • T (e 0) := T.map_smulₛₗ c (e 0)
    rw [ht] at h₂
    simp only [map_smul,LinearMap.smul_apply,smul_eq_mul] at h₂
    have he : (σ c - c) * form F (T (e 0)) w = 0 := by
      calc
        _ = (σ c * form F (T (e 0)) w + c * form F (T w) (e 0)) -
            c * (form F (T (e 0)) w + form F (T w) (e 0)) := by ring
        _ = 0 := by rw [h₁,h₂]; ring
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hw)
  ext c
  exact hs c

variable [Finite F] [CharP F 2]
/-- Realize a projective null polarity by a nondegenerate alternating form,
then use a symplectic basis to put it in the standard form. -/
theorem null_collineation_polar_equivalence (hF : Nat.card F ≠ 2)
    (φ : Equiv.Perm (ProjectivePoint F)) (hφ : Collineation.PreservesLines φ)
    (hn : ∀ p, Orthogonal (φ p) p) :
    ∃ E : Vector F ≃ₗ[F] Vector F, ∀ p r,
      Orthogonal (Collineation.linearProjective E p) (Collineation.linearProjective E r) ↔
        Orthogonal (φ p) r := by
  obtain ⟨σ,A,hlift⟩ := projective_permutation_has_semilinear_lift hF φ hφ
  have hn' (v : Vector F) : form F (A (fieldVector σ v)) v = 0 := by
    by_cases hv : v = 0
    · simp [hv]
    have hh := hn (mk F v hv)
    rw [hlift] at hh
    simpa only [fieldProjective,Equiv.coe_fn_mk,Projectivization.map_mk,
      orthogonal_mk_iff,LinearEquiv.coe_coe] using hh
  have hσ := null_semilinear_field_eq_id σ A hn'
  subst σ
  have hid (v : Vector F) : fieldVector (RingEquiv.refl F) v = v := rfl
  have hnA (v : Vector F) : form F (A v) v = 0 := by simpa only [hid] using hn' v
  let B : LinearMap.BilinForm F (Vector F) := (form F).comp A.toLinearMap LinearMap.id
  have hB : B.IsAlt := hnA
  have hBN : B.Nondegenerate := by
    constructor
    · intro v hv
      apply A.injective
      exact (TwoLocalCover.form_nondegenerate.1 (A v) hv).trans (map_zero A).symm
    · intro w hw
      apply TwoLocalCover.form_nondegenerate.2
      intro v
      obtain ⟨u,rfl⟩ := A.surjective v
      exact hw u
  obtain ⟨E⟩ := Matrix.PSp4Three.exists_isometry 2 B hB hBN (by simp [Theory.SpecificGroups.SymplecticFour.Vector])
  refine ⟨E.toLinearEquiv,?_⟩
  intro p r
  induction p using Projectivization.ind with | h v hv =>
  induction r using Projectivization.ind with | h w hw =>
  rw [hlift]
  simp only [Collineation.linearProjective_apply,Projectivization.map_mk,
    fieldProjective,Equiv.coe_fn_mk,hid,orthogonal_mk_iff,LinearEquiv.coe_coe]
  change Matrix.PSp4Three.form (E v) (E w) = 0 ↔ B v w = 0
  rw [E.map_app]

end Theory.GroupAction.SymplecticRankThree

namespace Theory.GroupAction.SymplecticRankThree.PolarityDesign
variable {Ω F : Type*} [Finite Ω] [Field F] [Finite F] [CharP F 2]

/-- Ordinary line coordinates determine polar coordinates: no pairing formula
or model map is required as input. Construction of the ordinary coordinates
from abstract incidence remains separate. -/
theorem polar_coordinates_of_line_coordinates (D : PolarityDesign Ω (Nat.card F))
    (hF : Nat.card F ≠ 2) (C : Ω ≃ ProjectivePoint F)
    (hC : ∀ x y z, (C z).submodule ≤ (C x).submodule ⊔ (C y).submodule ↔ z ∈ D.line x y) :
    ∃ E : Ω ≃ ProjectivePoint F, ∀ x y, Orthogonal (E x) (E y) ↔ D.incident x y := by
  obtain ⟨A,hA⟩ := null_collineation_polar_equivalence hF (D.coordinatePolarity C hC)
    (D.coordinatePolarity_preserves_lines C hC) (D.coordinatePolarity_null C hC)
  refine ⟨C.trans (Collineation.linearProjective A),?_⟩
  intro x y
  change Orthogonal (Collineation.linearProjective A (C x))
    (Collineation.linearProjective A (C y)) ↔ _
  rw [hA,coordinatePolarity_apply,coordinatePole_incident]

end Theory.GroupAction.SymplecticRankThree.PolarityDesign
