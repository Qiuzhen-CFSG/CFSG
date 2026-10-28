module
public import Theory.GroupAction.SymplecticRankThree.ProjectiveCompletion

/-!
# Constructed projective three-space over the source field

FieldSpace constructs a compatible affine chart from spatial projections.
ProjectiveCompletion adjoins every actual point at infinity and proves all line
equivalences. Finite-field uniqueness identifies the reconstructed scalar field
with the specified field of order q; a semilinear change of coordinates writes
the resulting projective chart in the standard four-coordinate vector carrier.
No field laws, coordinate chart or compatibility equations are assumed.

The nonbinary hypothesis is used only for the affine-combination proof of plane
closure. The separate binary recognition supplies the q=2 branch. Thus order
four and every larger binary field remain included in this construction.

Source: Higman (1964), Lemma 10 and Theorem 2(i), pp.153–155,
the expanded projective reconstruction and coordinatization step.
-/

public noncomputable section
open Projectivization
namespace Theory.GroupAction.SymplecticRankThree

section FieldMap
variable {K F : Type*} [Field K] [Field F] (σ : K ≃+* F)
local instance : RingHomInvPair σ.toRingHom σ.symm.toRingHom := RingHomInvPair.of_ringEquiv σ
local instance : RingHomInvPair σ.symm.toRingHom σ.toRingHom := RingHomInvPair.of_ringEquiv σ.symm

/-- Change the reconstructed field and write the four homogeneous coordinates
in the standard matrix-model vector carrier. -/
@[expose] def homogeneousFieldEquiv :
    (K × ((K × K) × K)) ≃ₛₗ[σ.toRingHom] ((Fin 2 ⊕ Fin 2) → F) where
  toFun u := Sum.elim ![σ u.1,σ u.2.1.1] ![σ u.2.1.2,σ u.2.2]
  invFun v := (σ.symm (v (.inl 0)),((σ.symm (v (.inl 1)),σ.symm (v (.inr 0))),σ.symm (v (.inr 1))))
  left_inv u := by simp
  right_inv v := by ext i; rcases i with i | i <;> fin_cases i <;> simp
  map_add' u v := by ext i; rcases i with i | i <;> fin_cases i <;> simp
  map_smul' r u := by ext i; rcases i with i | i <;> fin_cases i <;> simp [smul_eq_mul]

@[expose] def projectiveFieldEquiv :
    Projectivization K (K × ((K × K) × K)) ≃ Projectivization F ((Fin 2 ⊕ Fin 2) → F) where
  toFun := Projectivization.map (homogeneousFieldEquiv σ).toLinearMap (homogeneousFieldEquiv σ).injective
  invFun := Projectivization.map (homogeneousFieldEquiv σ).symm.toLinearMap (homogeneousFieldEquiv σ).symm.injective
  left_inv p := by
    induction p using Projectivization.ind with | h v hv =>
    simp only [map_mk,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply]
  right_inv p := by
    induction p using Projectivization.ind with | h v hv =>
    simp only [map_mk,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply]

theorem projectiveFieldEquiv_line
    (a b x : Projectivization K (K × ((K × K) × K))) :
    (projectiveFieldEquiv σ x).submodule ≤
      (projectiveFieldEquiv σ a).submodule ⊔ (projectiveFieldEquiv σ b).submodule ↔
        x.submodule ≤ a.submodule ⊔ b.submodule := by
  let E := homogeneousFieldEquiv σ
  induction a using Projectivization.ind with | h a ha =>
  induction b using Projectivization.ind with | h b hb =>
  induction x using Projectivization.ind with | h x hx =>
  change (Projectivization.map E.toLinearMap E.injective (Projectivization.mk _ x hx)).submodule ≤
    (Projectivization.map E.toLinearMap E.injective (Projectivization.mk _ a ha)).submodule ⊔
    (Projectivization.map E.toLinearMap E.injective (Projectivization.mk _ b hb)).submodule ↔ _
  simp only [map_mk,submodule_mk,← Submodule.span_insert,Submodule.span_singleton_le_iff_mem,
    Submodule.mem_span_pair,LinearEquiv.coe_coe]
  constructor
  · rintro ⟨r,s,hrs⟩
    refine ⟨σ.symm r,σ.symm s,E.injective ?_⟩
    rw [map_add,E.map_smulₛₗ,E.map_smulₛₗ]
    change σ (σ.symm r) • E a + σ (σ.symm s) • E b = E x
    simpa only [σ.apply_symm_apply] using hrs
  · rintro ⟨r,s,hrs⟩
    refine ⟨σ r,σ s,?_⟩
    have hh := congrArg E hrs
    rw [map_add,E.map_smulₛₗ,E.map_smulₛₗ] at hh
    exact hh

end FieldMap

/-- A nonbinary finite field supplies the two nonzero coefficients needed
to recover vector addition from affine lines. -/
theorem exists_scalar_ne_zero_one (K : Type*) [Field K] [Finite K] (hK : Nat.card K ≠ 2) :
    ∃ t : K, t ≠ 0 ∧ t ≠ 1 := by
  by_contra! hh
  have hsub : (Set.univ : Set K) ⊆ {0,1} := by
    intro t _
    by_cases ht : t = 0
    · exact Or.inl ht
    · exact Or.inr (hh t ht)
  have hn := Set.ncard_le_ncard hsub
  rw [Set.ncard_univ,Set.ncard_pair zero_ne_one] at hn
  have hp := Finite.one_lt_card (α := K)
  omega

namespace AffineFrame
variable {Ω : Type*} [Finite Ω] {q : ℕ} {D : PolarityDesign Ω q}
variable (f : AffineFrame D)
variable (hl : ∀ a b, a ≠ b → (D.line a b).ncard = q+1) (hq : 2 ≤ q)
local instance : Field (f.scalarRing hl hq) := f.scalarField hl hq

include f hl hq in
/-- The actual spatial geometry has one compatible projective coordinate
chart over the specified source field. No coordinates are an input. -/
theorem exists_projective_space_coordinates
    (F : Type*) [Field F] [Finite F] (hcard : q = Nat.card F) (hF : Nat.card F ≠ 2) :
    ∃ C : Ω ≃ Projectivization F ((Fin 2 ⊕ Fin 2) → F),
      ∀ a b x, (C x).submodule ≤ (C a).submodule ⊔ (C b).submodule ↔ x ∈ D.line a b := by
  obtain ⟨E,hE⟩ := f.exists_field_space_coordinates hl hq
  let C := FieldChart.ofLineEquiv E hE
  obtain ⟨t,ht0,ht1⟩ := exists_scalar_ne_zero_one (f.scalarRing hl hq)
    (by rw [f.scalarField_card hl hq,hcard]; exact hF)
  let σ := f.scalarFieldEquiv hl hq F hcard
  refine ⟨(C.projectiveEquiv hl hq).trans (projectiveFieldEquiv σ),?_⟩
  intro a b x
  exact (projectiveFieldEquiv_line σ _ _ _).trans (C.projectiveEquiv_line hl hq t ht0 ht1 a b x)

end AffineFrame
end Theory.GroupAction.SymplecticRankThree
