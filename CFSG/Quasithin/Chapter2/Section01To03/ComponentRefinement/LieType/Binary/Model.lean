module

public import Theory.SpecificGroups.BinaryLinear.Parabolics
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

/-!
# The binary component's actual linear action

The canonical quotient SLₙ(2) → PSLₙ(2) and the inclusion SLₙ(2) → GLₙ(2)
are isomorphisms. The resulting linear action of the projective group is
proved to be multiplication by the original matrix representative. Transport
through a supplied component isomorphism therefore retains the binary subspace
geometry and gives centerlessness without a simplicity assumption.

This is the model interface for the L₄(2) and L₅(2) calculations in
Aschbacher–Smith 2.3.9(7), combined manuscript, printed pp.525–526.
The center and determinant arguments extend the checked degree-three proof in
`Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel`.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary
open Subgroup

abbrev Vector (n : ℕ) := Fin n → ZMod 2
abbrev SL (n : ℕ) := Matrix.SpecialLinearGroup (Fin n) (ZMod 2)
abbrev PSL (n : ℕ) := Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)

theorem sl_center_eq_bot (n : ℕ) [NeZero n] : center (SL n) = ⊥ := by
  apply eq_bot_iff.mpr
  intro A hA
  change A = 1
  obtain ⟨a, ha, he⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have han : a ^ n = 1 := by simpa using ha
  have ha0 : a ≠ 0 := by
    intro hz
    simp [hz, NeZero.ne n] at han
  have ha1 : a = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) a ha0
  apply Subtype.ext
  simpa [ha1] using he.symm

noncomputable def slEquivPSL (n : ℕ) [NeZero n] : SL n ≃* PSL n :=
  MulEquiv.ofBijective (QuotientGroup.mk' (center (SL n)))
    ⟨by rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', sl_center_eq_bot],
      QuotientGroup.mk'_surjective _⟩

theorem slEquivPSL_apply (n : ℕ) [NeZero n] (A : SL n) :
    slEquivPSL n A = QuotientGroup.mk' (center (SL n)) A := rfl

private theorem toGL_surjective (n : ℕ) :
    Function.Surjective (Matrix.SpecialLinearGroup.toGL :
      SL n →* Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) := by
  intro A
  have hu : ∀ a : (ZMod 2)ˣ, a = 1 := by decide
  have hd : Matrix.det (A : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 :=
    congrArg Units.val (hu (Matrix.GeneralLinearGroup.det A))
  exact ⟨⟨A, hd⟩, Units.ext rfl⟩

noncomputable def slEquivLinear (n : ℕ) : SL n ≃* BinaryLinear.GL (Vector n) :=
  (MulEquiv.ofBijective Matrix.SpecialLinearGroup.toGL
    ⟨Matrix.SpecialLinearGroup.toGL_injective, by exact toGL_surjective n⟩).trans
      (Matrix.GeneralLinearGroup.toLin.trans
        (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Vector n)))

theorem slEquivLinear_apply (n : ℕ) (A : SL n) (v : Vector n) :
    slEquivLinear n A v = Matrix.mulVec A.val v := rfl

noncomputable def pslEquivLinear (n : ℕ) [NeZero n] :
    PSL n ≃* BinaryLinear.GL (Vector n) :=
  (slEquivPSL n).symm.trans (slEquivLinear n)

theorem pslEquivLinear_project (n : ℕ) [NeZero n] (A : SL n) (v : Vector n) :
    pslEquivLinear n (QuotientGroup.mk' (center (SL n)) A) v =
      Matrix.mulVec A.val v := by
  change slEquivLinear n ((slEquivPSL n).symm (slEquivPSL n A)) v = _
  rw [MulEquiv.symm_apply_apply, slEquivLinear_apply]

variable {G : Type*} [Group G] {L : Subgroup G} {n : ℕ} [NeZero n]

noncomputable def linearModel (e : L ≃* PSL n) : L ≃* BinaryLinear.GL (Vector n) :=
  e.trans (pslEquivLinear n)

theorem center_eq_bot (e : L ≃* PSL n) : center L = ⊥ := by
  let f := e.trans (slEquivPSL n).symm
  apply eq_bot_iff.mpr
  intro x hx
  have hc : f x ∈ center (SL n) := by
    rw [mem_center_iff]
    intro y
    obtain ⟨y, rfl⟩ := f.surjective y
    simpa only [← map_mul] using congrArg f (mem_center_iff.mp hx y)
  rw [sl_center_eq_bot, mem_bot] at hc
  exact f.injective (hc.trans (map_one f).symm)

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary

end
