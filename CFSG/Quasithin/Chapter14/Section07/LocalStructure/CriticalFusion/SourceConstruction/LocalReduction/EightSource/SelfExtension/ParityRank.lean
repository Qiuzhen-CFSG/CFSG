module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.SelfExtension.Model
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic

/-!
# Displacement obstructs a parity-twisted natural self-extension

For a binary block operator with upper-right block A D+D A+A, displacement
on the graph of D is injective: a zero image first forces Ay=y, and its
other coordinate then forces y=0. Thus the moved dimension is at least one
entire block, six in the natural S₈ module. The bound passes through any
injective intertwiner into the actual module under consideration.

Source: Aschbacher–Smith, Lemma 14.7.51, printed p.1065, refs/quasithin.pdf.
-/

public section
open Module
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.SelfExtension

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

/-- A binary parity-twisted doubled block moves at least the dimension of one block. -/
theorem finrank_le_parity_twist_displacement (a d : Module.End (ZMod 2) W)
    (T : Module.End (ZMod 2) (W × W))
    (hT : ∀ x y, T (x,y) = (a x + (a (d y) + d (a y) + a y), a y)) :
    finrank (ZMod 2) W ≤ finrank (ZMod 2) (T - 1).range := by
  let f : W →ₗ[ZMod 2] (T - 1).range :=
    (T - 1).rangeRestrict.comp (d.prod LinearMap.id)
  have htwo (x : W) : x+x=0 := by
    calc
      x+x = ((1+1 : ZMod 2) • x) := by rw [add_smul,one_smul]
      _ = 0 := by rw [show (1+1 : ZMod 2)=0 by decide,zero_smul]
  have hinj : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm _ bot_le
    intro y hy
    have hz : (T-1) (d y,y) = 0 := congrArg Subtype.val hy
    rw [LinearMap.sub_apply,hT] at hz
    have hy2 : a y-y=0 := congrArg Prod.snd hz
    have hy1 : a (d y) + (a (d y) + d (a y) + a y) - d y=0 := congrArg Prod.fst hz
    have ha : a y = y := sub_eq_zero.mp hy2
    rw [ha] at hy1
    have he : a (d y) + (a (d y) + d y + y) - d y = y := by
      calc
        _ = (a (d y) + a (d y)) + y := by abel
        _ = y := by rw [htwo,zero_add]
    exact he.symm.trans hy1
  exact LinearMap.finrank_le_finrank_of_injective hinj
/-- An injective intertwiner cannot decrease the displacement dimension. -/
theorem displacement_rank_le_of_injective_intertwining
    {F U X : Type*} [Field F] [AddCommGroup U] [Module F U]
    [AddCommGroup X] [Module F X] [FiniteDimensional F U] [FiniteDimensional F X]
    (j : U →ₗ[F] X) (hj : Function.Injective j)
    (t : Module.End F U) (f : Module.End F X)
    (h : ∀ u, f (j u)=j (t u)) :
    finrank F (t-1).range ≤ finrank F (f-1).range := by
  let k : (t-1).range →ₗ[F] (f-1).range :=
    (j.comp (t-1).range.subtype).codRestrict (f-1).range (by
      rintro ⟨v,w,rfl⟩
      refine ⟨j w,?_⟩
      simp only [LinearMap.comp_apply,Submodule.subtype_apply,
        LinearMap.sub_apply,Module.End.one_apply,map_sub,h])
  apply LinearMap.finrank_le_finrank_of_injective (f := k)
  intro u v huv
  exact Subtype.ext (hj (congrArg Subtype.val huv))

/-- Every parity-twisted six-dimensional block moves at least six dimensions. -/
theorem parity_twist_rank_ge_six (d : Module.End (ZMod 2) V)
    (T : Module.End (ZMod 2) (V × V))
    (hT : ∀ x y, T (x,y) = ((A 0).mulVec x +
      ((A 0).mulVec (d y) + d ((A 0).mulVec y) + (A 0).mulVec y), (A 0).mulVec y)) :
    6 ≤ finrank (ZMod 2) (T-1).range := by
  simpa only [V,Module.finrank_pi,Module.finrank_self,Fintype.card_fin,mul_one]
    using finrank_le_parity_twist_displacement (A 0).mulVecLin d T hT

/-- A parity-twisted block is incompatible with displacement at most two. -/
theorem parity_twist_rank_gt_two (d : Module.End (ZMod 2) V)
    (T : Module.End (ZMod 2) (V × V))
    (hT : ∀ x y, T (x,y) = ((A 0).mulVec x +
      ((A 0).mulVec (d y) + d ((A 0).mulVec y) + (A 0).mulVec y), (A 0).mulVec y)) :
    2 < finrank (ZMod 2) (T-1).range :=
  lt_of_lt_of_le (by decide) (parity_twist_rank_ge_six d T hT)

/-- Matrix form of the obstruction, retaining the arbitrary coboundary matrix. -/
theorem parity_twist_matrix_rank_gt_two (d : Mat)
    (T : Module.End (ZMod 2) (V × V))
    (hT : ∀ x y, T (x,y) = ((A 0).mulVec x +
      (A 0 * d + d * A 0 + A 0).mulVec y, (A 0).mulVec y)) :
    2 < finrank (ZMod 2) (T-1).range := by
  apply parity_twist_rank_gt_two d.mulVecLin T
  intro x y
  simpa only [Matrix.add_mulVec,Matrix.mulVecLin_apply,Matrix.mulVec_mulVec]
    using hT x y

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.SelfExtension
