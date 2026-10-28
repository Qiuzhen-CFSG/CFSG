module
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.Actor
public import Theory.SpecificGroups.PSL3.LinearThreeFlags
/-!
# Aligning the source point with the standard point parabolic

A nonzero marked-point vector extends to a determinant-one basis, by
transitivity of SL₃ on nonzero vectors. Conjugating by this basis identifies
the full marked-line stabilizer, and its genuine two-residual, with the
standard matrix subgroups. The natural action equation records the same
basis change on vectors, so subsequent local module calculations can use
the literal source actor.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
G.2.5(8), printed pp.335–336.
-/

@[expose] public section
open Subgroup Matrix
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction
open Matrix.PSL3.LinearThree
variable {G : Type*} [Group G] [Finite G] {D : Setup G}
  {F : Type*} [Field F] [Finite F] {n : ℕ} {g h : G}
  (d : Hypothesis D F n g h)

/-- A genuine determinant-one change of basis carrying the first coordinate
line onto the source's marked point. -/
structure PointAlignment where
  basis : SL(3, F)
  point_eq : (d.point : Set (Fin 3 → F)) =
    basis • {v : Fin 3 → F | v 1 = 0 ∧ v 2 = 0}

theorem exists_pointAlignment : Nonempty (PointAlignment d) := by
  have hp : d.point ≠ ⊥ := (Submodule.isAtom_iff_finrank_eq_one.mpr d.point_dimension).ne_bot
  obtain ⟨v, hv, hv0⟩ := d.point.ne_bot_iff.mp hp
  have he0 : (![1, 0, 0] : Fin 3 → F) ≠ 0 := by
    intro he
    have := congrFun he 0
    exact one_ne_zero this
  obtain ⟨b, hb⟩ := SpecialLinearGroup.exists_mulVec_eq_three _ v he0 hv0
  refine ⟨⟨b, ?_⟩⟩
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one d.point_dimension hv hv0
  ext w
  constructor
  · intro hw
    change w ∈ d.point at hw
    rw [hspan, Submodule.mem_span_singleton] at hw
    obtain ⟨a, rfl⟩ := hw
    refine ⟨a • (![1, 0, 0] : Fin 3 → F), by simp, ?_⟩
    change b.val *ᵥ (a • ![1, 0, 0]) = a • v
    rw [mulVec_smul, hb]
  · rintro ⟨u, hu, rfl⟩
    have he : u = u 0 • (![1, 0, 0] : Fin 3 → F) := by
      ext i
      fin_cases i <;> simp_all
    change b.val *ᵥ u ∈ d.point
    rw [he, mulVec_smul, hb]
    exact d.point.smul_mem _ hv

namespace PointAlignment
variable {d} (a : PointAlignment d)

theorem stabilizer_map :
    (markedStabilizer d).map (MulAut.conj a.basis⁻¹).toMonoidHom = pointParabolicSL F := by
  have hm (x : SL(3, F)) : x ∈ markedStabilizer d ↔
      a.basis⁻¹ * x * a.basis ∈ pointParabolicSL F := by
    change x • (d.point : Set (Fin 3 → F)) = d.point ↔
      (a.basis⁻¹ * x * a.basis) • {v : Fin 3 → F | v 1 = 0 ∧ v 2 = 0} = _
    rw [a.point_eq]
    rw [mul_smul, mul_smul]
    exact ⟨fun hx => by rw [hx, inv_smul_smul], fun hx => by
      have he := congrArg (fun s : Set (Fin 3 → F) => a.basis • s) hx
      simpa only [smul_inv_smul] using he⟩
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hm y |>.mp hy
  · intro hx
    refine ⟨a.basis * x * a.basis⁻¹, ?_, ?_⟩
    · apply (hm _).mpr
      simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hx
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group

/-- The source star map followed by this concrete change of basis. -/
def projection : D.L →* SL(3, F) :=
  (MulAut.conj a.basis⁻¹).toMonoidHom.comp (modelProjection d)

/-- Compatibility of the aligned actor with the literal natural coordinates. -/
theorem projection_natural (l : D.L) (v : Fin 3 → F) :
    a.projection l • (a.basis⁻¹ • v) =
      a.basis⁻¹ • (modelProjection d l • v) := by
  change (a.basis⁻¹ * modelProjection d l * (a.basis⁻¹)⁻¹) • (a.basis⁻¹ • v) = _
  rw [inv_inv, mul_smul, mul_smul, smul_inv_smul]

theorem residual_image :
    (D.L₁.subgroupOf D.L).map a.projection =
      (pResidual 2 (pointParabolicSL F)).map (pointParabolicSL F).subtype := by
  rw [projection, ← Subgroup.map_map, ResidualRestriction.residual_image,
    map_embedded_pResidual, a.stabilizer_map]

end PointAlignment
end CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction
