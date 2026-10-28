module

public import Theory.AtlasPort.ExceptionalIsomorphisms.FieldTransportLaws
public import Theory.SpecificGroups.SL2.SylowConsequences
public import Theory.GroupTheory.PCoreSurjective
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Algebra.CharP.Two

/-!
# Field automorphisms and the two-core of the rank-one quotient

Every scalar occurs as the trace of a determinant-one companion matrix.
Thus coefficientwise field transport can be inner on SL₂ only when the
field automorphism is trivial. In characteristic two the center of SL₂ is
trivial, so this also proves the assertion for the actual quotient PSL₂.
The defining-characteristic two-core lies in the upper-unipotent Sylow;
conjugation by the Weyl matrix forces its parameter to vanish.

Source: the local quotient argument in Aschbacher--Smith F.1.12, printed
p. 264. Field transport is the existing licensed ATLAS construction;
the trace and Sylow arguments here are independent elementary proofs.
-/

@[expose] public section

open Matrix
open scoped MatrixGroups
namespace Atlas.RankOneFieldAutomorphisms
variable {F : Type*} [Field F]

theorem field_eq_one_of_SL_inner (σ : F ≃+* F) (g : SL(2,F))
    (h : fieldEquivSL 2 σ = MulAut.conj g) : σ = 1 := by
  ext t
  let a : SL(2,F) := ⟨!![0, -1; 1, t], by simp [Matrix.det_fin_two]⟩
  have ht := congrArg (fun b : SL(2,F) => Matrix.trace b.val) (MulEquiv.congr_fun h a)
  have hc : Matrix.trace (g * a * g⁻¹).val = Matrix.trace a.val := by
    change Matrix.trace (g.val * a.val * (g⁻¹).val) = _
    rw [Matrix.trace_mul_cycle]
    change Matrix.trace ((g⁻¹ * g).val * a.val) = _
    simp
  change Matrix.trace (fieldEquivSL 2 σ a).val = Matrix.trace (g * a * g⁻¹).val at ht
  rw [hc] at ht
  simp only [Matrix.trace_fin_two] at ht
  change σ 0 + σ t = 0 + t at ht
  simpa using ht

theorem sl_center_eq_bot [CharP F 2] : Subgroup.center SL(2,F) = ⊥ := by
  apply (Subgroup.center SL(2,F)).eq_bot_iff_forall.mpr
  intro g hg
  obtain ⟨a, ha, he⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hg
  simp only [Fintype.card_fin] at ha
  have ha1 : a = 1 := by
    rcases sq_eq_one_iff.mp ha with h | h
    · exact h
    · simpa only [CharTwo.neg_eq] using h
  apply Subtype.ext
  simpa [ha1] using he.symm

theorem sl_project_injective [CharP F 2] :
    Function.Injective (QuotientGroup.mk' (Subgroup.center SL(2,F))) := by
  rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', sl_center_eq_bot]

theorem field_eq_one_of_PSL_inner [CharP F 2] (σ : F ≃+* F) (g : PSL(2,F))
    (h : fieldEquivPSL 2 σ = MulAut.conj g) : σ = 1 := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL(2,F)) g
  apply field_eq_one_of_SL_inner σ g
  apply MulEquiv.ext
  intro a
  apply sl_project_injective
  simpa only [fieldEquivPSL_mk, MulAut.conj_apply, map_mul, map_inv] using
    MulEquiv.congr_fun h (QuotientGroup.mk' _ a)

theorem sl_twoCore_eq_bot [Finite F] [CharP F 2] : pCore 2 SL(2,F) = ⊥ := by
  have hle : pCore 2 SL(2,F) ≤ Matrix.SpecialLinearGroup.upperUnipotent F :=
    pCore_isPGroup.le_sylow_of_normal (Matrix.SpecialLinearGroup.upperUnipotentSylow F 2)
  apply (pCore 2 SL(2,F)).eq_bot_iff_forall.mpr
  intro g hg
  obtain ⟨t, rfl⟩ := (Matrix.SpecialLinearGroup.mem_upperUnipotent F g).mp (hle hg)
  let w : SL(2,F) := ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩
  have hw := (inferInstance : (pCore 2 SL(2,F)).Normal).conj_mem _ hg w
  obtain ⟨s, hs⟩ := (Matrix.SpecialLinearGroup.mem_upperUnipotent F _).mp (hle hw)
  have he := congrArg (fun b : SL(2,F) => b.val 1 0) hs
  have hw_inv : (w⁻¹).val = !![0, 1; -1, 0] := by
    change Matrix.adjugate w.val = _
    simp [w, Matrix.adjugate_fin_two]
  have ht : t = 0 := by
    change (Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one s).val 1 0 =
      ((w.val * (Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one t).val) *
        (w⁻¹).val) 1 0 at he
    simpa [hw_inv, w, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] using he.symm
  rw [ht, Matrix.SpecialLinearGroup.transvection_coeff_zero]

noncomputable def slEquivPSL [CharP F 2] : SL(2,F) ≃* PSL(2,F) :=
  MulEquiv.ofBijective (QuotientGroup.mk' _) ⟨sl_project_injective,
    QuotientGroup.mk'_surjective _⟩

theorem psl_twoCore_eq_bot [Finite F] [CharP F 2] : pCore 2 PSL(2,F) = ⊥ := by
  rw [← pCore_map_iso 2 (slEquivPSL (F := F)), sl_twoCore_eq_bot, Subgroup.map_bot]

def slFieldAction : (F ≃+* F) →* MulAut SL(2,F) where
  toFun := fieldEquivSL 2
  map_one' := by
    apply MulEquiv.ext
    intro g
    rfl
  map_mul' σ τ := by
    apply MulEquiv.ext
    intro g
    rfl
theorem psl_center_eq_bot [CharP F 2] : Subgroup.center PSL(2,F) = ⊥ := by
  apply (Subgroup.center PSL(2,F)).eq_bot_iff_forall.mpr
  intro x hx
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL(2,F)) x
  have hg : g ∈ Subgroup.center SL(2,F) := by
    rw [Subgroup.mem_center_iff]
    intro a
    apply sl_project_injective
    simpa only [map_mul] using Subgroup.mem_center_iff.mp hx (QuotientGroup.mk' _ a)
  have hg1 : g = 1 := by simpa only [sl_center_eq_bot, Subgroup.mem_bot] using hg
  rw [hg1, map_one]

def pslFieldAction : (F ≃+* F) →* MulAut PSL(2,F) where
  toFun := fieldEquivPSL 2
  map_one' := by
    apply MulEquiv.ext
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL(2,F)) x
    rw [fieldEquivPSL_mk]
    rfl
  map_mul' σ τ := by
    apply MulEquiv.ext
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL(2,F)) x
    change fieldEquivPSL 2 (σ * τ) (QuotientGroup.mk' _ g) =
      fieldEquivPSL 2 σ (fieldEquivPSL 2 τ (QuotientGroup.mk' _ g))
    simp only [fieldEquivPSL_mk]
    rfl

end Atlas.RankOneFieldAutomorphisms
