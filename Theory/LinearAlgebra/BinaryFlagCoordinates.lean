module
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.RadicalOrientation.Basic
import Mathlib.Tactic.FinCases
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Coordinates on a binary point-plane flag

A linear isomorphism from a two-space to the standard coordinate plane can
be chosen to send a specified nonzero vector to the first coordinate.
Extend that isomorphism to the ambient four-space. Both the point and the
plane are then marked in one basis.

Source application: the natural flag V₂/V₁ ≤ V₃/V₁ in
Aschbacher--Smith, The Classification of Quasithin Groups,
13.8.29--30, printed p.964.
-/

@[expose] public noncomputable section
namespace BinaryLinear.FlagCoordinates
abbrev Four := Fin 4 → ZMod 2

def plane : Submodule (ZMod 2) Four where
  carrier := {v | v 2 = 0 ∧ v 3 = 0}
  zero_mem' := by simp
  add_mem' := by rintro x y ⟨hx,hx'⟩ ⟨hy,hy'⟩; simp_all
  smul_mem' := by rintro a x ⟨hx,hx'⟩; simp_all

private def planeCoordinates : (Fin 2 → ZMod 2) ≃ₗ[ZMod 2] plane where
  toFun x := ⟨![x 0,x 1,0,0],by constructor <;> rfl⟩
  invFun x := ![x.val 0,x.val 1]
  left_inv x := by ext i; fin_cases i <;> rfl
  right_inv x := by
    apply Subtype.ext
    ext i
    fin_cases i <;> try rfl
    · exact x.property.1.symm
    · exact x.property.2.symm
  map_add' x y := by apply Subtype.ext; ext i; fin_cases i <;> simp
  map_smul' a x := by apply Subtype.ext; ext i; fin_cases i <;> simp

theorem plane_finrank : Module.finrank (ZMod 2) plane = 2 := by
  rw [←planeCoordinates.finrank_eq,Module.finrank_fin_fun]

theorem first_mem_plane : (Pi.single 0 1 : Four) ∈ plane := by
  constructor <;> simp

theorem exists_plane_coordinates (P : Submodule (ZMod 2) Four)
    (hd : Module.finrank (ZMod 2) P = 2) (v : Four) (hv : v ∈ P) (hv0 : v ≠ 0) :
    ∃ E : Four ≃ₗ[ZMod 2] Four,
      E v = Pi.single 0 1 ∧ P.map E.toLinearMap = plane := by
  let f : P ≃ₗ[ZMod 2] plane := LinearEquiv.ofFinrankEq _ _ (hd.trans plane_finrank.symm)
  let w : plane := ⟨Pi.single 0 1,first_mem_plane⟩
  have hv' : (⟨v,hv⟩ : P) ≠ 0 := by intro he; exact hv0 (congrArg Subtype.val he)
  have hw : w ≠ 0 := by
    intro he
    have hh := congrArg (fun x : plane => x.val 0) he
    simp [w] at hh
  obtain ⟨a,ha⟩ := BinaryLinear.OuterCyclic.exists_linearEquiv_apply_eq (f.map_ne_zero_iff.mpr hv') hw
  let f' := f.trans a
  obtain ⟨E,hE⟩ := Submodule.exists_linearEquiv_restrict_eq f'
  refine ⟨E,(hE ⟨v,hv⟩).symm.trans (congrArg Subtype.val ha),?_⟩
  apply le_antisymm
  · rintro x ⟨y,hy,rfl⟩
    change E y ∈ plane
    rw [←hE ⟨y,hy⟩]
    exact (f' ⟨y,hy⟩).property
  · intro x hx
    refine ⟨f'.symm ⟨x,hx⟩,(f'.symm ⟨x,hx⟩).property,?_⟩
    simpa using (hE (f'.symm ⟨x,hx⟩)).symm

end BinaryLinear.FlagCoordinates
