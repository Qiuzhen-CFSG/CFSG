module
public import Theory.GroupTheory.CentralCyclicTwoRank
public import Theory.SpecificGroups.OddFourRank
public import Theory.SpecificGroups.SymplecticFour.Flag
public import BenderSuzuki.MatrixGroups.Unitary
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.LinearAlgebra.Transvection.Basic
public import Mathlib.LinearAlgebra.Center

/-!
# Odd-characteristic projective degree-four rank bounds

Determinant-one degree four has elementary two-rank at most three. Passing
through its actual central cyclic kernel gives projective two-rank at most
six. This applies to PSL₄, every stored SU₄ projective image, and PSp₄.
For the symplectic center, commuting with transvections forces scalar action.

Source: the bounds needed in Aschbacher–Smith 4.4.3, printed p.622. The
symplectic scalar argument follows the ATLAS transvection calculation already
ported in `SymplecticFour.EvenProjective`; its original ATLAS attribution and
license apply (LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff).
-/

public noncomputable section
open Subgroup Matrix
open scoped MatrixGroups
namespace Theory.SpecificGroups.OddFourProjectiveRank
variable {F : Type*} [Field F] [Finite F]

private theorem gl_center_cyclic {ι : Type*} [Fintype ι] [DecidableEq ι] :
    IsCyclic (center (GL ι F)) := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
  exact isCyclic_of_surjective _ (Matrix.GeneralLinearGroup.scalar ι (R := F)).rangeRestrict_surjective

/-- The actual projective special linear group in degree four has two-rank at most six. -/
theorem psl_four_twoRank_le_six (h2 : (2 : F) ≠ 0) : primeRank 2 PSL(4,F) ≤ 6 := by
  let : IsCyclic (center SL(4,F)) :=
    Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity.isCyclic.mpr inferInstance
  let f := QuotientGroup.mk' (center SL(4,F))
  let : IsCyclic f.ker := by change IsCyclic (QuotientGroup.mk' (center SL(4,F))).ker; rw [QuotientGroup.ker_mk']; infer_instance
  exact CentralCyclicRank.twoRank_le_double f (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk'])
    (OddFourRank.twoRank_le_three SpecialLinearGroup.toGL SpecialLinearGroup.toGL_injective
      h2 SpecialLinearGroup.coeToGL_det)

/-- The actual projective image of every special unitary four-space has two-rank at most six. -/
theorem psu_four_twoRank_le_six (J : BenderSuzuki.MatrixGroups.HermitianForm 4 F)
    (h2 : (2 : F) ≠ 0) :
    primeRank 2 (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) ≤ 6 := by
  let f := Matrix.ProjGenLinGroup.mk.subgroupMap J.specialSubgroup
  have hf : Function.Surjective f := Matrix.ProjGenLinGroup.mk.subgroupMap_surjective J.specialSubgroup
  let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective f hf
  have hscalar (x : f.ker) : x.val.val ∈ center (GL (Fin 4) F) := by
    apply Matrix.ProjGenLinGroup.mk_eq_one.mp
    exact congrArg Subtype.val (MonoidHom.mem_ker.mp x.property)
  let j : f.ker →* center (GL (Fin 4) F) :=
    (J.specialSubgroup.subtype.comp f.ker.subtype).codRestrict _ hscalar
  have hj : Function.Injective j := by
    intro a b hab
    exact Subtype.ext (Subtype.ext (congrArg (fun z : center (GL (Fin 4) F) => (z : GL (Fin 4) F)) hab))
  let : IsCyclic (center (GL (Fin 4) F)) := gl_center_cyclic
  let : IsCyclic f.ker := isCyclic_of_injective j hj
  have hc : f.ker ≤ center J.specialSubgroup := by
    intro x hx
    exact mem_center_iff.mpr fun y => Subtype.ext
      (mem_center_iff.mp (hscalar ⟨x,hx⟩) y.val)
  exact CentralCyclicRank.twoRank_le_double f hf hc
    (OddFourRank.twoRank_le_three J.specialSubgroup.subtype J.specialSubgroup.subtype_injective
      h2 (fun s => s.property.2))
end Theory.SpecificGroups.OddFourProjectiveRank

namespace Theory.SpecificGroups.SymplecticFour.OddProjectiveRank
variable {F : Type*} [Field F]
private def toGL : Sp F →* GL (Fin 2 ⊕ Fin 2) F where
  toFun g := Matrix.GeneralLinearGroup.mk'' g.val (SymplecticGroup.symplectic_det g.property)
  map_one' := by apply Units.ext; rfl
  map_mul' _ _ := by apply Units.ext; rfl

private theorem toGL_injective : Function.Injective (toGL (F := F)) := by
  intro x y h
  exact Subtype.ext (congrArg Units.val h)

private theorem form_self (v : Vector F) : form F v v = 0 := by
  simp [form_apply, mul_comm]

private theorem form_swap (v w : Vector F) : form F v w = -form F w v := by
  simp only [form_apply, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

private def transvectionMap (v : Vector F) : Module.End F (Vector F) :=
  LinearMap.transvection ((form F).flip v) v

private theorem transvectionMap_apply (v x : Vector F) :
    transvectionMap v x = x + form F x v • v := rfl

private def transvection (v : Vector F) : Sp F :=
  ⟨LinearMap.toMatrix' (transvectionMap v), by
    apply SymplecticGroup.mem_iff'.mpr
    have he := Matrix.toBilin'_comp (-Matrix.J (Fin 2) F)
      (LinearMap.toMatrix' (transvectionMap v)) (LinearMap.toMatrix' (transvectionMap v))
    have hpres : (form F).comp (transvectionMap v) (transvectionMap v) = form F := by
      apply LinearMap.ext
      intro x
      apply LinearMap.ext
      intro y
      change form F (transvectionMap v x) (transvectionMap v y) = form F x y
      simp only [transvectionMap_apply, map_add, map_smul, LinearMap.add_apply,
        LinearMap.smul_apply, smul_eq_mul, form_self, mul_zero, add_zero]
      rw [form_swap v y]
      ring
    simp only [Matrix.toLin'_toMatrix'] at he
    have hm := Matrix.toBilin'.injective (he.symm.trans hpres)
    simpa [Matrix.mul_neg, Matrix.neg_mul, form] using hm⟩

private theorem transvection_apply (v x : Vector F) :
    transvection v • x = x + form F x v • v := by
  change (LinearMap.toMatrix' (transvectionMap v)) *ᵥ x = _
  rw [LinearMap.toMatrix'_mulVec, transvectionMap_apply]

private theorem exists_form_left {v : Vector F} (hv : v ≠ 0) :
    ∃ x, form F x v = 1 := by
  have hex : ∃ w, form F w v ≠ 0 := by
    by_contra! h
    apply hv
    funext i
    cases i with
    | inl i =>
      have hi := h (Pi.single (.inr i) 1)
      simpa [form_apply, Pi.single_apply] using hi
    | inr i =>
      have hi := h (e i)
      simpa [form_apply, e, Pi.single_apply] using hi
  obtain ⟨w, hw⟩ := hex
  exact ⟨(form F w v)⁻¹ • w, by simp [map_smul, hw]⟩

private theorem central_preserves_lines (g : Sp F) (hg : g ∈ Subgroup.center (Sp F))
    (v : Vector F) (hv : v ≠ 0) : ∃ a : F, a • v = g • v := by
  obtain ⟨x, hx⟩ := exists_form_left hv
  have h := congrArg (fun t : Sp F => t • x)
    (Subgroup.mem_center_iff.mp hg (transvection v))
  simp only [mul_smul, transvection_apply] at h
  change g • x + form F (g • x) v • v = toLinear g (x + form F x v • v) at h
  rw [(toLinear g).map_add, (toLinear g).map_smul, hx, one_smul] at h
  exact ⟨form F (g • x) v, add_left_cancel h⟩

private theorem central_is_scalar (g : Sp F) (hg : g ∈ Subgroup.center (Sp F)) :
    ∃ a : F, ∀ x : Vector F, g • x = a • x := by
  obtain ⟨a, ha⟩ := (toLinear g).toLinearMap.exists_eq_smul_id_of_forall_notLinearIndependent
    (fun v => by
      by_cases hv : v = 0
      · simp [hv, linearIndependent_fin2]
      · rw [LinearIndependent.pair_iff' hv]
        obtain ⟨a, ha⟩ := central_preserves_lines g hg v hv
        exact fun h => h a ha)
  exact ⟨a, fun x => congrArg (fun l : Vector F →ₗ[F] Vector F => l x) ha⟩


private theorem central_toGL (g : Sp F) (hg : g ∈ center (Sp F)) :
    toGL g ∈ center (GL (Fin 2 ⊕ Fin 2) F) := by
  apply Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr
  obtain ⟨a, ha⟩ := central_is_scalar g hg
  refine ⟨a, ?_⟩
  change (Matrix.scalar (Fin 2 ⊕ Fin 2) a) = g.val
  ext i j
  have h := congrFun (ha (Pi.single j 1)) i
  simpa [smul_eq_mulVec, Matrix.mulVec_single, Matrix.scalar_apply,
    Matrix.diagonal, Pi.single_apply, smul_eq_mul, eq_comm] using h.symm

/-- The genuine symplectic center is cyclic over a finite field. -/
theorem center_isCyclic [Finite F] : IsCyclic (center (Sp F)) := by
  let j : center (Sp F) →* center (GL (Fin 2 ⊕ Fin 2) F) :=
    (toGL.comp (center (Sp F)).subtype).codRestrict _
      (fun g => central_toGL g.val g.property)
  have hj : Function.Injective j := by
    intro a b hab
    exact Subtype.ext (toGL_injective (congrArg Subtype.val hab))
  let : IsCyclic (center (GL (Fin 2 ⊕ Fin 2) F)) :=
    Theory.SpecificGroups.OddFourProjectiveRank.gl_center_cyclic
  exact isCyclic_of_injective j hj

/-- The four-dimensional symplectic central quotient has two-rank at most six. -/
theorem twoRank_le_six [Finite F] (h2 : (2 : F) ≠ 0) :
    primeRank 2 (Sp F ⧸ center (Sp F)) ≤ 6 := by
  let e : (Fin 2 ⊕ Fin 2) ≃ Fin 4 := finSumFinEquiv
  let r : GL (Fin 2 ⊕ Fin 2) F ≃* GL (Fin 4) F :=
    Units.mapEquiv (Matrix.reindexRingEquiv F e).toMulEquiv
  let ρ := r.toMonoidHom.comp toGL
  have hρ : Function.Injective ρ := r.injective.comp toGL_injective
  have hdet (g : Sp F) : Matrix.GeneralLinearGroup.det (ρ g) = 1 := by
    apply Units.ext
    change Matrix.det (Matrix.reindex e e g.val) = 1
    rw [Matrix.det_reindex_self]
    exact SymplecticGroup.det_eq_one g.property
  let : IsCyclic (center (Sp F)) := center_isCyclic
  let f := QuotientGroup.mk' (center (Sp F))
  let : IsCyclic f.ker := by change IsCyclic (QuotientGroup.mk' (center (Sp F))).ker; rw [QuotientGroup.ker_mk']; infer_instance
  exact CentralCyclicRank.twoRank_le_double f (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk'])
    (Theory.SpecificGroups.OddFourRank.twoRank_le_three ρ hρ h2 hdet)
end Theory.SpecificGroups.SymplecticFour.OddProjectiveRank
