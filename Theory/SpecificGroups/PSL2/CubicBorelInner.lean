module

public import Theory.GroupAction.CubicBorelInner
public import Theory.FieldTheory.CubicTorusDisplacement
public import Theory.SpecificGroups.SL2.EvenBorelResidual.Semilinear
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear.SemilinearCoverage


/-!
# Inner cubic automorphisms of a binary PSL₂ Borel

An arbitrary automorphism of the actual projective matrix group is inner
followed by a coefficient automorphism, by the proved semilinear coverage
theorem. Sylow conjugacy aligns its invariant Sylow subgroup with the upper
root group. The inner factor then lies in the actual upper Borel and acts
trivially on its torus quotient.

For a cubic actor, its coefficient automorphism is cubic too. If every
Borel displacement is three-primary modulo the root group, the coefficient
displacement image on the field units is a three-group. The fixed-field
cardinality calculation forces that coefficient automorphism to be trivial.
Thus the original actor is inner. No coverage, field-action, or innerness
hypothesis remains in the theorem.

Source: Aschbacher--Smith, the rank-one paragraph of 15.3.37,
`refs/quasithin.pdf`, printed p.1135. The explicit Sylow/Borel alignment
and coefficient-action identities come from `EvenBorelResidual.Semilinear`;
semilinear coverage uses GLS4, Chapter 4, Lemma 3.1(a).
-/

@[expose] public section

open scoped MatrixGroups
open Subgroup BenderSuzuki.Converse Atlas
namespace Matrix.ProjectiveSpecialLinearGroup
open OddBorel EvenBorelResidual.Semilinear

private theorem benderFieldAut_eq_fieldEquiv {F : Type*} [Field F] [CharP F 2]
    (σ : F ≃+* F) :
    BenderSuzuki.ZD.Linear.fieldAut σ = Atlas.fieldEquivPSL 2 σ := by
  ext x
  obtain ⟨g, rfl⟩ := BenderSuzuki.Converse.pi_surjective x
  rw [BenderSuzuki.ZD.Linear.fieldAut_apply_pi]
  change _ = Atlas.fieldEquivPSL 2 σ (QuotientGroup.mk' _ g)
  rw [Atlas.fieldEquivPSL_mk]
  rfl

/-- The actual binary PSL₂ group satisfies the cubic Borel innerness detector. -/
theorem cubicBorelInner (F : Type*) [Field F] [Finite F] [CharP F 2] :
    MulAut.CubicBorelInner (PSL(2,F)) := by
  intro P α hα hP hB
  have hPmap : (P : Subgroup PSL(2,F)).map α.toMonoidHom = P := by
    have hle : (P : Subgroup PSL(2,F)).map α.toMonoidHom ≤ P := by
      rintro _ ⟨x, hx, rfl⟩
      exact hP x hx
    let Q : Sylow 2 PSL(2,F) := P.mapSurjective (f := α.toMonoidHom) α.surjective
    have hQ : (Q : Subgroup PSL(2,F)) = (P : Subgroup PSL(2,F)).map α.toMonoidHom := rfl
    have hmax : (P : Subgroup PSL(2,F)) = Q :=
      Q.is_maximal' P.isPGroup' (by simpa [hQ] using hle)
    exact hQ.symm.trans hmax.symm
  have hcoverage : ∀ β : MulAut PSL(2,F),
      ∃ (g : PSL(2,F)) (σ : F ≃+* F), β = MulAut.conj g * Atlas.fieldEquivPSL 2 σ := by
    intro β
    obtain ⟨g, σ, hg⟩ := BenderSuzuki.ZD.Linear.semilinear_coverage β
    refine ⟨g, σ, hg.trans ?_⟩
    rw [benderFieldAut_eq_fieldEquiv]
  obtain ⟨c, g, σ, hcU, hcB, hβ⟩ :=
    aligned_semilinear_of_coverage F P α hPmap hcoverage
  let e := MulAut.conj c
  let β := MulAut.congr e.symm α
  have hβpow : β ^ 3 = 1 := by
    dsimp [β]
    rw [← map_pow, hα, map_one]
  have hσpow : σ ^ 3 = 1 := field_pow_eq_one_of_actor_pow F g σ 3 (hβ ▸ hβpow)
  have hUpre : (P : Subgroup PSL(2,F)).comap e.toMonoidHom = kernel F := by
    rw [← hcU]
    exact comap_map_eq_self_of_injective e.injective _
  have hdisplace (b : PSL(2,F)) (hb : b ∈ borel F) :
      ∃ k : ℕ, (β b * b⁻¹) ^ (3 ^ k) ∈ kernel F := by
    have hbn : e b ∈ normalizer (P : Set PSL(2,F)) :=
      hcB ▸ mem_map_of_mem e.toMonoidHom hb
    obtain ⟨k, hk⟩ := hB (e b) hbn
    refine ⟨k, ?_⟩
    rw [← hUpre]
    change e ((β b * b⁻¹) ^ (3 ^ k)) ∈ P
    rw [map_pow, map_mul, map_inv]
    change (e (e.symm (α (e b))) * (e b)⁻¹) ^ (3 ^ k) ∈ P
    rwa [e.apply_symm_apply]
  have hu (u : Fˣ) : ∃ k : ℕ,
      (FiniteField.BinaryTorusInvolution.displacement σ u) ^ (3 ^ k) = 1 := by
    let b : borel F := ⟨torusHom F u, (show complement F ≤ borel F from le_sup_right) ⟨u, rfl⟩⟩
    obtain ⟨k, hk⟩ := hdisplace b b.property
    have ht : torusProjection F ((borelActor F g σ b * b⁻¹) ^ (3 ^ k)) = 1 := by
      apply (torusProjection_eq_one_iff F _).mpr
      change ((MulAut.conj (g : PSL(2,F)) * fieldEquivPSL 2 σ) b * (b : PSL(2,F))⁻¹) ^
        (3 ^ k) ∈ kernel F
      rw [← hβ]
      exact hk
    rw [map_pow, map_mul, map_inv, torusProjection_borelActor] at ht
    have hbproj : torusProjection F b = u := torusProjection_torus F u
    rw [hbproj] at ht
    exact ⟨k, ht⟩
  have hp : IsPGroup 3 (FiniteField.BinaryTorusInvolution.displacement σ).range := by
    rintro ⟨_, u, rfl⟩
    obtain ⟨k, hk⟩ := hu u
    exact ⟨k, Subtype.ext hk⟩
  have hσ : σ = 1 :=
    FiniteField.CubicTorusDisplacement.eq_one_of_three_primary_displacement σ hσpow hp
  have hfieldone : Atlas.fieldEquivPSL 2 (1 : F ≃+* F) = 1 := by
    change Atlas.RankOneFieldAutomorphisms.pslFieldAction (1 : F ≃+* F) = 1
    exact Atlas.RankOneFieldAutomorphisms.pslFieldAction.map_one
  have hinner : MulAut.congr e.symm α ∈ MulAut.innerSubgroup PSL(2,F) := by
    refine ⟨(g : PSL(2,F)), ?_⟩
    rw [hβ, hσ, hfieldone, mul_one]
  rw [← MulAut.map_innerSubgroup_congr e.symm] at hinner
  obtain ⟨a, ha, he⟩ := hinner
  exact (MulAut.congr e.symm).injective he ▸ ha

end Matrix.ProjectiveSpecialLinearGroup
