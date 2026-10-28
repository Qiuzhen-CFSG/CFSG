module
public import Theory.Representation.BinaryParabolicExteriorSquare.PlaneRadical
public import Theory.GroupTheory.SubgroupConjugation
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.FinCases

/-!
# Hyperplane fixers in the binary plane radical

Write the plane radical of SL₄(2) as the upper-right two-by-two block.
Fixing any vector outside its common fixed plane gives one nonzero linear
constraint on each row. The remaining two binary coordinates determine an
actor, so every subgroup fixing a natural hyperplane has order at most four.
Transport by the original matrix conjugator retains the same bound.

This supplies the upper-image calculation in Aschbacher–Smith,
The Classification of Quasithin Groups, 13.8.32(3), printed p.965.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace Representation.BinaryParabolicExteriorSquare.PlaneRadical
open PlaneSpan

private theorem fixed_coordinates (v w : Four)
    (h : Matrix.mulVec (matrix v) w = w) :
    v 0 * w 2 + v 2 * w 3 = 0 ∧ v 1 * w 2 + v 3 * w 3 = 0 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1
  exact ⟨h0,h1⟩

/-- Fixing a vector outside the natural fixed plane leaves at most two binary parameters. -/
theorem card_le_four_of_fixed_vector (A : Subgroup SL) (hA : A ≤ radical) (w : Four)
    (hw : w 2 ≠ 0 ∨ w 3 ≠ 0)
    (hfix : ∀ a : A, Matrix.mulVec a.val.val w = w) : Nat.card A ≤ 4 := by
  let c (a : A) : Four := (coordinates ⟨a,hA a.property⟩).toAdd
  have he (a : A) : matrix (c a) = a.val.val :=
    congrArg Subtype.val (element_coordinates ⟨a,hA a.property⟩)
  have hc (a : A) := fixed_coordinates (c a) w (by rw [he]; exact hfix a)
  have hi : Function.Injective c := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    rw [←he a,←he b,hab]
  rcases hw with hw | hw
  · let f (a : A) : Fin 2 → Bit := ![c a 2,c a 3]
    have hf : Function.Injective f := by
      intro a b hab
      have h2eq : c a 2 = c b 2 := congrFun hab 0
      have h3eq : c a 3 = c b 3 := congrFun hab 1
      apply hi
      ext i
      fin_cases i
      · have ha := (hc a).1
        have hb := (hc b).1
        rw [h2eq] at ha
        exact mul_right_cancel₀ hw (add_right_cancel (ha.trans hb.symm))
      · have ha := (hc a).2
        have hb := (hc b).2
        rw [h3eq] at ha
        exact mul_right_cancel₀ hw (add_right_cancel (ha.trans hb.symm))
      · exact h2eq
      · exact h3eq
    exact (Nat.card_le_card_of_injective f hf).trans_eq (by simp [Bit])
  · let f (a : A) : Fin 2 → Bit := ![c a 0,c a 1]
    have hf : Function.Injective f := by
      intro a b hab
      have h0eq : c a 0 = c b 0 := congrFun hab 0
      have h1eq : c a 1 = c b 1 := congrFun hab 1
      apply hi
      ext i
      fin_cases i
      · exact h0eq
      · exact h1eq
      · have ha := (hc a).1
        have hb := (hc b).1
        rw [h0eq] at ha
        exact mul_right_cancel₀ hw (add_left_cancel (ha.trans hb.symm))
      · have ha := (hc a).2
        have hb := (hc b).2
        rw [h1eq] at ha
        exact mul_right_cancel₀ hw (add_left_cancel (ha.trans hb.symm))
    exact (Nat.card_le_card_of_injective f hf).trans_eq (by simp [Bit])

/-- A hyperplane contains a vector outside the radical's fixed natural plane. -/
theorem exists_vector_outside_fixed_plane (P : Submodule Bit Four)
    (hP : Module.finrank Bit P = 3) :
    ∃ w ∈ P, w 2 ≠ 0 ∨ w 3 ≠ 0 := by
  classical
  by_contra! h
  let f : P →ₗ[Bit] (Fin 2 → Bit) := {
    toFun w := ![w.val 0,w.val 1]
    map_add' v w := by ext i; fin_cases i <;> rfl
    map_smul' a w := by ext i; fin_cases i <;> rfl }
  have hf : Function.Injective f := by
    intro v w he
    apply Subtype.ext
    ext i
    fin_cases i
    · exact congrFun he 0
    · exact congrFun he 1
    · exact (h v v.property).1.trans (h w w.property).1.symm
    · exact (h v v.property).2.trans (h w w.property).2.symm
  have hd := LinearMap.finrank_le_finrank_of_injective hf
  simp only [hP,Module.finrank_pi, Fintype.card_fin] at hd
  omega

/-- The pointwise stabilizer of a natural hyperplane inside the plane radical
has order at most four. -/
theorem card_le_four_of_fixed_hyperplane (A : Subgroup SL) (hA : A ≤ radical)
    (P : Submodule Bit Four) (hP : Module.finrank Bit P = 3)
    (hfix : ∀ a : A, ∀ w ∈ P, Matrix.mulVec a.val.val w = w) : Nat.card A ≤ 4 := by
  obtain ⟨w,hw,hn⟩ := exists_vector_outside_fixed_plane P hP
  exact card_le_four_of_fixed_vector A hA w hn (fun a => hfix a w hw)


/-- Conjugating the original parabolic preserves the bound and its hyperplane. -/
theorem card_le_four_of_fixed_hyperplane_conjugate (A : Subgroup SL) (g : SL)
    (hA : A ≤ radical.conjBy g) (P : Submodule Bit Four)
    (hP : Module.finrank Bit P = 3)
    (hfix : ∀ a : A, ∀ w ∈ P, Matrix.mulVec a.val.val w = w) : Nat.card A ≤ 4 := by
  let B := A.conjBy g⁻¹
  have hB : B ≤ radical := by
    have hh := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hA
    change B ≤ (radical.conjBy g).conjBy g⁻¹ at hh
    rwa [conjBy_inv] at hh
  let E := Matrix.SpecialLinearGroup.toLin' g⁻¹
  let P' := P.map E.toLinearMap
  have hp : Module.finrank Bit P' = 3 := (E.finrank_map_eq P).trans hP
  have hb (b : B) (w : Four) (hw : w ∈ P') : Matrix.mulVec b.val.val w = w := by
    obtain ⟨a,ha,he⟩ := b.property
    obtain ⟨v,hv,rfl⟩ := hw
    have hfa : Matrix.SpecialLinearGroup.toLin' a v = v := hfix ⟨a,ha⟩ v hv
    change Matrix.SpecialLinearGroup.toLin' b.val (E v) = E v
    simp only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv] at he
    rw [←he]
    dsimp only [E]
    simp only [map_mul,map_inv,LinearEquiv.mul_apply]
    simp only [LinearEquiv.coe_inv,LinearEquiv.apply_symm_apply,hfa]
  have hc := card_le_four_of_fixed_hyperplane B hB P' hp hb
  have he : Nat.card B = Nat.card A := card_map_of_injective (MulAut.conj g⁻¹).injective
  rwa [he] at hc

end Representation.BinaryParabolicExteriorSquare.PlaneRadical
