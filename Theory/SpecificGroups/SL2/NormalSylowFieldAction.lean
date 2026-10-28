module

public import Theory.SpecificGroups.SL2.EvenBorelResidual.Semilinear

/-!
# Normalizer displacements detect the field part of a rank-one actor

Let an inner--field automorphism preserve a Sylow two-subgroup of SL₂ or
PSL₂ over a finite field of characteristic two. If its displacements on
the Sylow normalizer lie in that Sylow, its field coefficient is trivial.

Conjugate the specified Sylow to the upper root group. This changes the
inner factor but keeps the original field coefficient. The inner factor
then lies in the upper Borel; projecting to its unipotent quotient shows
that the coefficient fixes every field unit, hence the whole field.
The SL₂ statement uses its literal central projection, which is an
isomorphism in characteristic two. No order restriction on the actor and
no prior torus fixation or innerness assumption is used.

Source: the normal-Sylow implication in Aschbacher--Smith F.1.12,
printed p.264 (PDF p.275); the quotient calculation is the existing
`EvenBorelResidual.Semilinear` torus projection.
-/

public section

open scoped MatrixGroups
open Subgroup BenderSuzuki.Converse Atlas
open Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual
open Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.Semilinear
open Matrix.ProjectiveSpecialLinearGroup.OddBorel
namespace Atlas.RankOneFieldAutomorphisms.NormalSylow
variable (F : Type*) [Field F] [Finite F] [CharP F 2]

/-- Trivial normalizer displacements force the original PSL₂ field coefficient to vanish. -/
theorem field_eq_one_of_normalizer_displacements (P : Sylow 2 PSL(2,F)) (g : PSL(2,F)) (σ : F ≃+* F)
    (hP : (P : Subgroup PSL(2,F)).map
      (MulAut.conj g * fieldEquivPSL 2 σ).toMonoidHom = P)
    (hd : ∀ x ∈ normalizer (P : Set PSL(2,F)),
      x⁻¹ * (MulAut.conj g * fieldEquivPSL 2 σ) x ∈ (P : Subgroup PSL(2,F))) : σ = 1 := by
  obtain ⟨c, hcU, hcB⟩ := sylow_normalizer_conjugate F P
  let e := MulAut.conj c
  let a := MulAut.conj g * fieldEquivPSL 2 σ
  let b := MulAut.congr e.symm a
  let d := c⁻¹ * g * fieldEquivPSL 2 σ c
  have hb : b = MulAut.conj d * fieldEquivPSL 2 σ := by
    ext x
    change c⁻¹ * (g * fieldEquivPSL 2 σ (c * x * c⁻¹) * g⁻¹) * c =
      d * fieldEquivPSL 2 σ x * d⁻¹
    simp only [map_mul, map_inv, d]
    group
  have hbU : (kernel F).map b.toMonoidHom = kernel F := by
    calc
      _ = (((kernel F).map e.toMonoidHom).map a.toMonoidHom).map e.symm.toMonoidHom := by
        rw [Subgroup.map_map, Subgroup.map_map]
        rfl
      _ = (P : Subgroup PSL(2,F)).map e.symm.toMonoidHom := by rw [hcU, hP]
      _ = kernel F := (map_symm_eq_iff_map_eq (kernel F) (e := e)).mpr hcU
  have hdB : d ∈ borel F := inner_factor_mem_borel F d σ (hb ▸ hbU)
  have hdisp (x : borel F) : (x : PSL(2,F))⁻¹ * b x ∈ kernel F := by
    have hx : e x ∈ normalizer (P : Set PSL(2,F)) := by
      rw [← hcB]
      exact mem_map_of_mem e.toMonoidHom x.property
    have hh := hd (e x) hx
    rw [← hcU] at hh
    obtain ⟨y, hy, he⟩ := hh
    have he' : y = (x : PSL(2,F))⁻¹ * b x := by
      apply e.injective
      change e y = (e x)⁻¹ * a (e x) at he
      rw [he, map_mul, map_inv]
      congr 1
      exact (e.apply_symm_apply (a (e x))).symm
    exact he' ▸ hy
  have hu (u : Fˣ) : Units.map σ.toMonoidHom u = u := by
    obtain ⟨x, rfl⟩ := torusProjection_surjective F u
    have hh : torusProjection F (x⁻¹ * borelActor F ⟨d, hdB⟩ σ x) = 1 := by
      apply (torusProjection_eq_one_iff F _).mpr
      change (x : PSL(2,F))⁻¹ * (MulAut.conj d * fieldEquivPSL 2 σ) x ∈ kernel F
      rw [← hb]
      exact hdisp x
    rw [map_mul, map_inv, torusProjection_borelActor, inv_mul_eq_one] at hh
    exact hh.symm
  ext x
  by_cases hx : x = 0
  · subst x; exact map_zero _
  · exact congrArg Units.val (hu (Units.mk0 x hx))


/-- The same criterion for the actual determinant-one two-by-two block. -/
theorem sl_field_eq_one_of_normalizer_displacements (P : Sylow 2 SL(2,F)) (g : SL(2,F)) (σ : F ≃+* F)
    (hP : (P : Subgroup SL(2,F)).map
      (MulAut.conj g * RankOneFieldAutomorphisms.slFieldAction σ).toMonoidHom = P)
    (hd : ∀ x ∈ normalizer (P : Set SL(2,F)),
      x⁻¹ * (MulAut.conj g * RankOneFieldAutomorphisms.slFieldAction σ) x ∈
        (P : Subgroup SL(2,F))) : σ = 1 := by
  let e := RankOneFieldAutomorphisms.slEquivPSL (F := F)
  let a := MulAut.conj g * RankOneFieldAutomorphisms.slFieldAction σ
  let b := MulAut.conj (e g) * fieldEquivPSL 2 σ
  have hab (x : SL(2,F)) : b (e x) = e (a x) := by
    change e g * fieldEquivPSL 2 σ (QuotientGroup.mk' _ x) * (e g)⁻¹ = _
    rw [fieldEquivPSL_mk]
    change e g * e (fieldEquivSL 2 σ x) * (e g)⁻¹ = e (g * fieldEquivSL 2 σ x * g⁻¹)
    rw [map_mul, map_mul, map_inv]
  have he : b.toMonoidHom.comp e.toMonoidHom = e.toMonoidHom.comp a.toMonoidHom := by
    ext x
    exact hab x
  apply field_eq_one_of_normalizer_displacements F (P.mapSurjective e.surjective) (e g) σ
  · change ((P : Subgroup SL(2,F)).map e.toMonoidHom).map b.toMonoidHom = _
    rw [Subgroup.map_map, he, ← Subgroup.map_map, hP]
    rfl
  · intro x hx
    have hx' : x ∈ (normalizer (P : Set SL(2,F))).map e.toMonoidHom := by
      change x ∈ (normalizer ((P : Subgroup SL(2,F)) : Set SL(2,F))).map e.toMonoidHom
      rw [map_equiv_normalizer_eq (P : Subgroup SL(2,F)) e]
      exact hx
    obtain ⟨y, hy, rfl⟩ := hx'
    change (e y)⁻¹ * b (e y) ∈ (P : Subgroup SL(2,F)).map e.toMonoidHom
    rw [hab, ← map_inv, ← map_mul]
    exact mem_map_of_mem e.toMonoidHom (hd y hy)
end Atlas.RankOneFieldAutomorphisms.NormalSylow
