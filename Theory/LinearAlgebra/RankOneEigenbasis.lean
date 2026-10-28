module
public import Mathlib.LinearAlgebra.Transvection.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.Basis.Fin

/-!
# Eigenbases for rank-one displacements

An invertible operator with rank-one displacement and determinant different
from one has a fixed plane complementary to its moved line. Writing it as
a dilatransvection identifies the moved eigenvalue with its determinant.
Joining bases of the two summands produces the literal diagonal matrix.

Source: the elementary linear-algebra step in Aschbacher--Smith H.2, p.378.
-/
public section
open Matrix Module Submodule
namespace LinearEquiv
variable {F : Type*} [Field F]

/-- A rank-one displacement with nontrivial determinant splits as a fixed
plane and its determinant eigenspace. -/
theorem exists_rank_one_eigenbasis (e : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F))
    (hr : finrank F (LinearMap.range (e.toLinearMap - LinearMap.id)) = 1)
    (hd : e.det ≠ 1) :
    ∃ b : Basis (Fin 3) F (Fin 3 → F),
      LinearMap.toMatrix b b e.toLinearMap = Matrix.diagonal ![1,1,(e.det : F)] := by
  classical
  obtain ⟨f,v,he⟩ := mem_dilatransvections_iff_finrank.mpr hr.le
  have hdet : (e.det : F) = 1 + f v := by
    rw [coe_det,he,LinearMap.transvection.det]
  have hfv : f v ≠ 0 := by
    intro hz
    apply hd
    apply Units.ext
    simpa [hz] using hdet
  have hv : v ≠ 0 := by intro hz; apply hfv; simp [hz]
  have hf : f ≠ 0 := by intro hz; apply hfv; simp [hz]
  let U := F ∙ v
  have hdis : Disjoint (LinearMap.ker f) U := by
    rw [disjoint_iff,Submodule.eq_bot_iff]
    rintro x ⟨hfx,hx⟩
    obtain ⟨c,rfl⟩ := mem_span_singleton.mp hx
    change f (c • v) = 0 at hfx
    have hc : c = 0 := (mul_eq_zero.mp (by simpa using hfx)).resolve_right hfv
    simp [hc]
  have hcomp := Module.Dual.isCompl_ker_of_disjoint_of_ne_bot hf hdis
    (show U ≠ ⊥ from (Submodule.span_singleton_eq_bot.not.mpr hv))
  have hker : finrank F (LinearMap.ker f) = 2 := by
    have hh := Module.Dual.finrank_ker_add_one_of_ne_zero hf
    simp only [Module.finrank_pi,Fintype.card_fin] at hh
    omega
  have hU : finrank F U = 1 := finrank_span_singleton hv
  let b0 := Module.finBasisOfFinrankEq F (LinearMap.ker f) hker
  let b1 := Module.finBasisOfFinrankEq F U hU
  let E := (LinearMap.ker f).prodEquivOfIsCompl U hcomp
  let b : Basis (Fin 3) F (Fin 3 → F) := ((b0.prod b1).map E).reindex finSumFinEquiv
  have hb0 : b 0 = (b0 0 : Fin 3 → F) := by
    simp only [b,Basis.reindex_apply,Basis.map_apply]
    change E ((b0.prod b1) (finSumFinEquiv.symm (Fin.castAdd 1 (0 : Fin 2)))) = _
    rw [finSumFinEquiv_symm_apply_castAdd]
    simp [E]
  have hb1 : b 1 = (b0 1 : Fin 3 → F) := by
    simp only [b,Basis.reindex_apply,Basis.map_apply]
    change E ((b0.prod b1) (finSumFinEquiv.symm (Fin.castAdd 1 (1 : Fin 2)))) = _
    rw [finSumFinEquiv_symm_apply_castAdd]
    simp [E]
  have hb2 : b 2 = (b1 0 : Fin 3 → F) := by
    simp only [b,Basis.reindex_apply,Basis.map_apply]
    change E ((b0.prod b1) (finSumFinEquiv.symm (Fin.natAdd 2 (0 : Fin 1)))) = _
    rw [finSumFinEquiv_symm_apply_natAdd]
    simp [E]
  have hew (w : Fin 3 → F) : e w = w + f w • v := LinearMap.congr_fun he w
  have h0 : e (b 0) = b 0 := by rw [hb0,hew]; simp
  have h1 : e (b 1) = b 1 := by rw [hb1,hew]; simp
  have h2 : e (b 2) = (e.det : F) • b 2 := by
    rw [hb2]
    obtain ⟨c,hc⟩ := mem_span_singleton.mp (b1 0).property
    rw [←hc,hew,LinearMap.map_smul,hdet]
    ext i
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    ring
  refine ⟨b,?_⟩
  ext i j
  fin_cases j <;> fin_cases i <;>
    simp [LinearMap.toMatrix_apply,h0,h1,h2]
end LinearEquiv
