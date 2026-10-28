module
public import Theory.SpecificGroups.SL2.EvenBorelResidual.Semilinear
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear.SemilinearCoverage

/-!
# Coprime binary PSL₂ actors on the actual Borel

Semilinear coverage writes a root-preserving automorphism as an inner
Borel factor followed by a coefficient automorphism. Coprimality excludes
a nonidentity inner actor; the coefficient order divides the original
actor order. The inner factor is retained, allowing a Sylow-aligned
marking without assuming that its diagonal torus is invariant.

Source: Aschbacher--Smith 11.5.6(3), printed p.781, and GLS4 Chapter 4,
Lemma 3.1(a). The entrywise-action comparison uses the existing coverage.
-/

public noncomputable section
open Subgroup BenderSuzuki.Converse Atlas
open scoped MatrixGroups
namespace Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.Semilinear
open OddBorel
variable (F : Type*) [Field F] [Finite F] [CharP F 2]

/-- The semilinear recognition action agrees with the literal entrywise action. -/
theorem exists_inner_field (α : MulAut PSL(2,F)) :
    ∃ (g : PSL(2,F)) (σ : F ≃+* F), α = MulAut.conj g * fieldEquivPSL 2 σ := by
  obtain ⟨g,σ,h⟩ := BenderSuzuki.ZD.Linear.semilinear_coverage α
  refine ⟨g,σ,h.trans ?_⟩
  congr 1
  ext z
  obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (center SL(2,F)) z
  rw [fieldEquivPSL_mk]
  exact BenderSuzuki.ZD.Linear.fieldAut_apply_pi σ a

/-- A nontrivial coprime root stabilizer has a nontrivial coefficient actor. -/
theorem exists_borel_inner_field_of_coprime
    (α : MulAut PSL(2,F)) (hne : α ≠ 1)
    (hc : Nat.Coprime (orderOf α) (Nat.card PSL(2,F)))
    (hr : (kernel F).map α.toMonoidHom = kernel F) :
    ∃ (g : borel F) (σ : F ≃+* F),
      σ ≠ 1 ∧ orderOf σ ∣ orderOf α ∧
      α = MulAut.conj (g : PSL(2,F)) * fieldEquivPSL 2 σ := by
  obtain ⟨g,σ,he⟩ := exists_inner_field F α
  have hg : g ∈ borel F := inner_factor_mem_borel F g σ (he ▸ hr)
  refine ⟨⟨g,hg⟩,σ,?_,?_,he⟩
  · intro hσ
    have hfield : fieldEquivPSL 2 σ = 1 := by
      change RankOneFieldAutomorphisms.pslFieldAction σ = 1
      rw [hσ,map_one]
    apply hne
    apply orderOf_eq_one_iff.mp
    apply Nat.eq_one_of_dvd_coprimes hc dvd_rfl
    rw [he,hfield,mul_one]
    exact (orderOf_map_dvd MulAut.conj g).trans (orderOf_dvd_natCard g)
  · exact orderOf_dvd_of_pow_eq_one (field_pow_eq_one_of_actor_pow F ⟨g,hg⟩ σ
      (orderOf α) (he ▸ pow_orderOf_eq_one α))
end Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.Semilinear
