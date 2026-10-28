module

public import Theory.SpecificGroups.Rudvalis.Multiplier.DoubleCover.Relations
public import Theory.SpecificGroups.Rudvalis.Multiplier.Perfect
public import Theory.GroupTheory.PerfectCentralCover
import Mathlib.Tactic.Group

/-!
# A concrete finite extension of the fixed Rudvalis model

Generate pairs of the degree-28 ATLAS matrices and the corresponding elements
of the degree-4060 model. Projection onto the second factor is surjective.
The checked matrix relations force perfectness, and the square of the first
pair is a nonidentity involution in the kernel. Scalarity of the whole kernel
is isolated as the remaining geometric input; it is not inferred from the
semi-presentation.

Source: ATLAS `2RuG1-f5r28B0`, and Aschbacher–Smith I.1.1–I.1.3, p.407.
-/

namespace Rudvalis.Multiplier.DoubleCover
public section

@[expose] def pairSubgroup : Subgroup (Matˣ × Rudvalis.Model) :=
  Subgroup.closure {(A, Rudvalis.a), (B, Rudvalis.b)}

/-- Pairs in the explicitly generated matrix/permutation subgroup. -/
@[expose] def Raw : Type := pairSubgroup
  deriving Group, Finite

@[expose] def a : Raw :=
  ⟨(A, Rudvalis.a), Subgroup.subset_closure (Set.mem_insert _ _)⟩

@[expose] def b : Raw :=
  ⟨(B, Rudvalis.b), Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩

/-- The projection has the original model as its literal codomain. -/
@[expose] def projection : Raw →* Rudvalis.Model :=
  (MonoidHom.snd Matˣ Rudvalis.Model).comp pairSubgroup.subtype

@[simp] theorem projection_a : projection a = Rudvalis.a := rfl
@[simp] theorem projection_b : projection b = Rudvalis.b := rfl

theorem projection_surjective : Function.Surjective projection := by
  apply MonoidHom.range_eq_top.mp
  exact Rudvalis.eq_top_of_a_mem_of_b_mem projection.range ⟨a, rfl⟩ ⟨b, rfl⟩

private theorem eq_top_of_generators (H : Subgroup Raw) (ha : a ∈ H) (hb : b ∈ H) : H = ⊤ := by
  have hle : pairSubgroup ≤ H.map pairSubgroup.subtype := by
    apply (Subgroup.closure_le _).mpr
    rintro x (rfl | hx)
    · exact ⟨a, ha, rfl⟩
    · obtain rfl := Set.mem_singleton_iff.mp hx
      exact ⟨b, hb, rfl⟩
  apply top_le_iff.mp
  intro x _
  obtain ⟨y, hy, hxy⟩ := hle x.property
  exact (Subtype.ext hxy : y = x) ▸ hy

theorem a_fourth : a ^ 4 = 1 := by
  apply Subtype.ext
  apply Prod.ext
  · exact A_fourth
  · change Rudvalis.a ^ 4 = 1
    rw [show 4 = 2 * 2 from rfl, pow_mul, Rudvalis.a_sq, one_pow]

theorem b_fourth : b ^ 4 = 1 := Subtype.ext (Prod.ext B_fourth Rudvalis.b_fourth)

theorem ab_thirteenth : (a * b) ^ 13 = 1 :=
  Subtype.ext (Prod.ext AB_thirteenth Rudvalis.ab_thirteenth)

theorem w_twentyNinth : (a * b * a * b * b) ^ 29 = 1 :=
  Subtype.ext (Prod.ext W_twentyNinth Rudvalis.w_twentyNinth)

/-- Perfectness follows from the actual four checked relations. -/
instance raw_isPerfect : Group.IsPerfect Raw := by
  let q : Raw →* Abelianization Raw := Abelianization.of
  have ha : q a ^ 4 = 1 := by rw [← map_pow, a_fourth, map_one]
  have hb : q b ^ 4 = 1 := by rw [← map_pow, b_fourth, map_one]
  have hab : (q a * q b) ^ 13 = 1 := by
    rw [← map_mul, ← map_pow, ab_thirteenth, map_one]
  have hab4 : (q a * q b) ^ 4 = 1 := by rw [mul_pow, ha, hb, one_mul]
  have hx : q a * q b = 1 := by
    have h : (q a * q b) ^ 13 = q a * q b := by
      calc
        _ = ((q a * q b) ^ 4) ^ 3 * (q a * q b) := by rw [← pow_mul]; exact pow_succ _ 12
        _ = q a * q b := by rw [hab4]; simp
    exact h.symm.trans hab
  have hw : q b ^ 29 = 1 := by
    have hqw : q (a * b * a * b * b) = q b := by simp only [map_mul, hx, one_mul]
    rw [← hqw, ← map_pow, w_twentyNinth, map_one]
  have hb1 : q b = 1 := by
    have h : q b ^ 29 = q b := by
      calc
        _ = (q b ^ 4) ^ 7 * q b := by group
        _ = q b := by rw [hb]; simp
    exact h.symm.trans hw
  have ha1 : q a = 1 := by simpa only [hb1, mul_one] using hx
  refine ⟨eq_top_of_generators (commutator Raw) ?_ ?_⟩
  · rw [← Abelianization.ker_of]
    exact ha1
  · rw [← Abelianization.ker_of]
    exact hb1

@[expose] def z : Raw := a ^ 2

theorem z_sq : z ^ 2 = 1 := by rw [z, ← pow_mul]; exact a_fourth

theorem projection_z : projection z = 1 := by rw [z, map_pow, projection_a, Rudvalis.a_sq]

theorem z_matrix : z.val.1 = -1 := A_sq

theorem z_ne_one : z ≠ 1 := by
  intro h
  have hmatrix : (-1 : Matˣ) = 1 := z_matrix.symm.trans (congrArg (fun x : Raw => x.val.1) h)
  have hentry := congrArg (fun u : Matˣ => (u : Mat) 0 0) hmatrix
  have he : (-1 : ZMod 5) = 1 := by simpa using hentry
  exact (by decide : (-1 : ZMod 5) ≠ 1) he

/-- Every kernel matrix is a scalar. The producer must establish this on the
actual paired subgroup, using the projective degree-4060 action. -/
@[expose] def ScalarKernel : Prop :=
  ∀ x : Raw, projection x = 1 →
    ∃ u : (ZMod 5)ˣ, x.val.1 = Matrix.GeneralLinearGroup.scalar (Fin 28) u

theorem ker_le_center_of_scalarKernel (h : ScalarKernel) :
    projection.ker ≤ Subgroup.center Raw := by
  intro x hx
  obtain ⟨u, hu⟩ := h x hx
  apply Subgroup.mem_center_iff.mpr
  intro y
  apply Subtype.ext
  apply Prod.ext
  · change y.val.1 * x.val.1 = x.val.1 * y.val.1
    rw [hu]
    exact (Matrix.GeneralLinearGroup.scalar_commute u y.val.1).symm
  · change y.val.2 * x.val.2 = x.val.2 * y.val.2
    change x.val.2 = 1 at hx
    rw [hx, mul_one, one_mul]

/-- A genuine cover conditional only on the outstanding scalar-kernel calculation. -/
@[expose] def coverOfScalarKernel (h : ScalarKernel) : PerfectCentralCovering.Cover Raw Rudvalis.Model where
  toMonoidHom := projection
  surjective := projection_surjective
  isPerfect := inferInstance
  ker_le_center := ker_le_center_of_scalarKernel h

end
end Rudvalis.Multiplier.DoubleCover
