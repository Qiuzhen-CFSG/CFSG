module
public import Theory.Representation.SpecialLinearNatural
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Data.ZMod.Basic

/-!
# Saturation of invariant Hom spaces for the binary three-space

Let U be a linear subspace of Hom(F₂³,T), stable under precomposition by
SL₃(2), where T has trivial action. A transvection difference isolates a
single row value; a second transvection moves it to any row. Thus if all
evaluations of U span T, every row with every value lies in U, and U is
the whole Hom space. Inverse transpose gives the identical result for the
literal dual natural action. The target need not be finite-dimensional.

Source application: Meierfrankenfeld–Stellmacher, Pushing up weak BN-pairs
of rank two (1993), the core-center argument (4.5), printed pp.895 and 899.
-/

@[expose] public section
namespace Representation.BinaryThreeHom
abbrev W := Fin 3 → ZMod 2
abbrev S := Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)
variable {T : Type*} [AddCommGroup T] [Module (ZMod 2) T]

private def row (j : Fin 3) : T →ₗ[ZMod 2] (W →ₗ[ZMod 2] T) where
  toFun t := (LinearMap.proj j).smulRight t
  map_add' t u := by ext v; simp [smul_add]
  map_smul' a t := by ext v; simp [smul_smul, mul_comm]

private theorem row_apply (j : Fin 3) (t : T) (v : W) : row j t v = v j • t := rfl

private theorem row_isolate (f : W →ₗ[ZMod 2] T) {i j : Fin 3} (hij : i ≠ j) :
    f.comp (specialLinearNatural 3 (Matrix.SpecialLinearGroup.transvection hij 1)) - f =
      row j (f (Pi.single i 1)) := by
  apply LinearMap.ext
  intro v
  change f (((1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) + Matrix.single i j 1).mulVec v) - f v = _
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq, one_mul, map_add]
  rw [map_smul, add_sub_cancel_left, row_apply]

/-- An invariant Hom subspace is saturated once its evaluations span the target. -/
theorem eq_top_of_evaluation_span
    (U : Submodule (ZMod 2) (W →ₗ[ZMod 2] T))
    (hU : ∀ g : S, ∀ f ∈ U, f.comp (specialLinearNatural 3 g) ∈ U)
    (hspan : Submodule.span (ZMod 2) {t | ∃ f ∈ U, ∃ v : W, f v = t} = ⊤) : U = ⊤ := by
  have hoff (f : W →ₗ[ZMod 2] T) (hf : f ∈ U) (i j : Fin 3) (hij : i ≠ j) :
      row j (f (Pi.single i 1)) ∈ U := by
    rw [← row_isolate f hij]
    exact U.sub_mem (hU _ f hf) hf
  have hrow (f : W →ₗ[ZMod 2] T) (hf : f ∈ U) (i j : Fin 3) :
      row j (f (Pi.single i 1)) ∈ U := by
    by_cases hij : i = j
    · subst j
      obtain ⟨k,hki⟩ := exists_ne i
      have h := hoff (row k (f (Pi.single i 1))) (hoff f hf i k hki.symm) k i hki
      simpa only [row_apply, Pi.single_eq_same, one_smul] using h
    · exact hoff f hf i j hij
  have hev (f : W →ₗ[ZMod 2] T) (hf : f ∈ U) (v : W) (j : Fin 3) : row j (f v) ∈ U := by
    have he : v = ∑ i : Fin 3, v i • (Pi.single i (1 : ZMod 2) : W) := by
      ext i
      simp [Pi.single_apply]
    rw [he, map_sum, map_sum]
    apply U.sum_mem
    intro i _
    rw [map_smul, map_smul]
    exact U.smul_mem (v i) (hrow f hf i j)
  have hall (j : Fin 3) (t : T) : row j t ∈ U := by
    have ht : t ∈ Submodule.span (ZMod 2) {t | ∃ f ∈ U, ∃ v : W, f v = t} := by
      rw [hspan]
      trivial
    induction ht using Submodule.span_induction with
    | mem t ht => obtain ⟨f,hf,v,rfl⟩ := ht; exact hev f hf v j
    | zero => simp
    | add t u ht hu hi hj => simpa only [map_add] using U.add_mem hi hj
    | smul a t ht hi => simpa only [map_smul] using U.smul_mem a hi
  apply top_unique
  intro f _
  have he : f = ∑ j : Fin 3, row j (f (Pi.single j 1)) := by
    apply LinearMap.ext
    intro v
    simp only [LinearMap.sum_apply, row_apply]
    simp_rw [← map_smul]
    rw [← map_sum]
    congr 1
    ext j
    simp [Pi.single_apply]
  rw [he]
  exact U.sum_mem (fun j _ => hall j _)

/-- The literal inverse-transpose action on the binary dual three-space. -/
def dualAction (g : S) : W →ₗ[ZMod 2] W :=
  specialLinearNatural 3 (Matrix.SpecialLinearGroup.transpose g⁻¹)

@[simp] theorem dualAction_apply (g : S) (v : W) :
    dualAction g v = (g⁻¹).val.transpose.mulVec v := rfl

@[simp] theorem dualAction_inv_apply (g : S) (v : W) :
    dualAction g⁻¹ (dualAction g v) = v := by
  simp only [dualAction_apply, inv_inv, Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
    ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one, Matrix.one_mulVec]

/-- The same saturation statement for the actual contragredient module. -/
theorem eq_top_of_dual_evaluation_span
    (U : Submodule (ZMod 2) (W →ₗ[ZMod 2] T))
    (hU : ∀ g : S, ∀ f ∈ U, f.comp (dualAction g) ∈ U)
    (hspan : Submodule.span (ZMod 2) {t | ∃ f ∈ U, ∃ v : W, f v = t} = ⊤) : U = ⊤ := by
  apply eq_top_of_evaluation_span U _ hspan
  intro g f hf
  have h := hU (Matrix.SpecialLinearGroup.transpose g)⁻¹ f hf
  have he : dualAction (Matrix.SpecialLinearGroup.transpose g)⁻¹ = specialLinearNatural 3 g := by
    unfold dualAction
    rw [inv_inv]
    congr 1
  rwa [he] at h
end Representation.BinaryThreeHom
