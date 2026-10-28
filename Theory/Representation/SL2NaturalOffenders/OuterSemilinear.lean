module
public import Theory.Representation.CentralCoverOriginalAction.Quadratic
public import Theory.Representation.SL2NaturalOffenders.Semilinear
public import Theory.SpecificGroups.PSL2.SemilinearCoverage
public import Theory.LinearAlgebra.SemilinearTrace

/-!
# The nontrivial field coefficient of an outer natural-module actor

The natural SL₂ scalar commutant makes every compatible binary automorphism
semilinear. If its field coefficient were trivial, similarity would preserve
all matrix traces. Inner-field automorphism coverage and the companion matrices
then force the quotient actor to be inner. Thus an outer involution acts with
a nontrivial involutory field coefficient on its literal natural module.

Source application: Aschbacher–Smith, Lemma 2.4.12(2), printed p.532.
-/

public section
noncomputable section
namespace Representation.SL2NaturalOffenders
open Matrix
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

theorem outer_intertwiner_semilinear
    (a : MulAut (Matrix.SpecialLinearGroup (Fin 2) F))
    (e : (Fin 2 → F) ≃ₗ[ZMod 2] (Fin 2 → F))
    (he : ∀ g v, e (g.val.mulVec v) = (a g).val.mulVec (e v))
    (houter : ¬ ∃ g, a = MulAut.conj g) :
    ∃ σ : F ≃+* F, σ ≠ RingEquiv.refl F ∧
      ∀ c v, e (c • v) = σ c • e v := by
  obtain ⟨σ,hσ⟩ := OneCohomology.CentralCoverOriginalAction.normalizer_semilinear
    (specialLinearNatural 2 (k := F)) (fun f hf => centralizer_scalar f hf) a e he
  refine ⟨σ,?_,hσ⟩
  intro hσid
  let E : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F) :=
    { e.toAddEquiv with
      map_smul' := by
        intro c v
        change e (c • v) = c • e v
        simpa only [hσid, RingEquiv.refl_apply] using hσ c v }
  have htrace (g : Matrix.SpecialLinearGroup (Fin 2) F) : (a g).val.trace = g.val.trace := by
    have hconj : E.conj g.val.toLin' = (a g).val.toLin' := by
      apply LinearMap.ext
      intro v
      change e (g.val.mulVec (e.symm v)) = (a g).val.mulVec v
      rw [he,e.apply_symm_apply]
    have hh := LinearMap.trace_conj' g.val.toLin' E
    rw [hconj, Matrix.trace_toLin'_eq, Matrix.trace_toLin'_eq] at hh
    exact hh
  obtain ⟨g,δ,ha⟩ := Theory.PSL2.sl2_semilinear_coverage a
  have hδ : δ = RingEquiv.refl F := by
    ext t
    let k : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![0,-1;1,t],by simp [Matrix.det_fin_two]⟩
    have ht := htrace k
    have hconj : (g * Theory.PSL2.sl2FieldAut δ k * g⁻¹).val.trace =
        (Theory.PSL2.sl2FieldAut δ k).val.trace := by
      change Matrix.trace (g.val * (Theory.PSL2.sl2FieldAut δ k).val * (g⁻¹).val) = _
      rw [Matrix.trace_mul_cycle]
      change Matrix.trace ((g⁻¹ * g).val * (Theory.PSL2.sl2FieldAut δ k).val) = _
      simp
    rw [ha] at ht
    change (g * Theory.PSL2.sl2FieldAut δ k * g⁻¹).val.trace = k.val.trace at ht
    rw [hconj] at ht
    simp only [Matrix.trace_fin_two] at ht
    change δ 0 + δ t = 0 + t at ht
    simpa using ht
  apply houter
  refine ⟨g,?_⟩
  rw [ha,hδ]
  ext k i j
  change (g * Theory.PSL2.sl2FieldAut (RingEquiv.refl F) k * g⁻¹).val i j = (g*k*g⁻¹).val i j
  rfl

omit [Finite F] [CharP F 2] in
theorem semilinear_coefficient_involutive
    (e : (Fin 2 → F) ≃ₗ[ZMod 2] (Fin 2 → F))
    (he : Function.Involutive e) (σ : F ≃+* F)
    (hσ : ∀ c v, e (c • v) = σ c • e v) : Function.Involutive σ := by
  intro c
  have hh := he (c • (![(1:F),0] : Fin 2 → F))
  rw [hσ,hσ,he] at hh
  have h0 := congrFun hh 0
  simpa using h0
end Representation.SL2NaturalOffenders
