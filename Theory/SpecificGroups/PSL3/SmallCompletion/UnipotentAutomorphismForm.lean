module

public import Theory.SpecificGroups.PSL3.LinearAmbientGeometry.CenterAction

/-!
# Ordered root-plane automorphisms of the native unitriangular group

The literal commutator pairing recovers one common field automorphism.
The only remaining freedom consists of two additive central corrections.
This is the coordinate normal form used in whole-Borel compatibility;
no endpoint extension or compatibility assumption is made.
-/

public noncomputable section
open Subgroup
open scoped commutatorElement
namespace Matrix.PSL3.SmallCompletion
open Matrix.PSL3Even.UnipotentGeometry
variable {F : Type*} [Field F] [Finite F]

omit [Finite F] in
private theorem comm_coordinates (u v : U F) :
    ⁅u,v⁆ = central F (Multiplicative.ofAdd (u.x*v.y-v.x*u.y)) := by
  apply U.ext <;> simp only [commutatorElement_def,mul_x,mul_y,mul_c]
  all_goals dsimp [Inv.inv,central]
  all_goals ring

/-- Exact coordinate normal form, on the original unitriangular carrier. -/
theorem ordered_root_plane_automorphism_form (a : MulAut (U F))
    (h₁ : ∀ u ∈ V₁ F, a u ∈ V₁ F)
    (h₂ : ∀ u ∈ V₂ F, a u ∈ V₂ F) :
    ∃ (r s : F) (σ : F ≃+* F) (f g : F →+ F),
      r ≠ 0 ∧ s ≠ 0 ∧ ∀ u : U F,
        a u = ⟨r*σ u.x,s*σ u.y,r*s*σ u.c+f u.x+g u.y⟩ := by
  obtain ⟨c,σ,hc,hσ⟩ := Matrix.PSL3.LinearAmbientGeometry.center_semilinear a h₁ h₂
  let X (x : F) : U F := ⟨x,0,0⟩
  let Y (y : F) : U F := ⟨0,y,0⟩
  have hx (x : F) : (a (X x)).y = 0 := (mem_V₁ F _).mp (h₁ _ (by simp [X]))
  have hy (y : F) : (a (Y y)).x = 0 := (mem_V₂ F _).mp (h₂ _ (by simp [Y]))
  have hcross (x y : F) : c*σ (x*y) = (a (X x)).x*(a (Y y)).y := by
    have hh := map_commutatorElement a (X x) (Y y)
    rw [comm_coordinates,comm_coordinates] at hh
    simp only [X,Y,zero_mul,sub_zero] at hh
    rw [hσ] at hh
    have hxx := hx x
    have hyy := hy y
    dsimp [X] at hxx
    dsimp [Y] at hyy
    simpa [central,hxx,hyy,X,Y] using congrArg U.c hh
  let r := (a (X 1)).x
  let s := (a (Y 1)).y
  have hrs : c = r*s := by simpa only [mul_one,map_one] using hcross 1 1
  have hr : r ≠ 0 := by intro hh; apply hc; rw [hrs,hh,zero_mul]
  have hs : s ≠ 0 := by intro hh; apply hc; rw [hrs,hh,mul_zero]
  have hax (x : F) : (a (X x)).x = r*σ x := by
    apply mul_right_cancel₀ hs
    have hh := hcross x 1
    simpa only [mul_one,hrs,mul_assoc,mul_comm s] using hh.symm
  have hay (y : F) : (a (Y y)).y = s*σ y := by
    apply mul_left_cancel₀ hr
    have hh := hcross 1 y
    simpa only [one_mul,hrs,mul_assoc] using hh.symm
  let f : F →+ F := {
    toFun x := (a (X x)).c
    map_zero' := by change (a 1).c=0; rw [map_one,one_c]
    map_add' x y := by
      have hh := congrArg U.c (map_mul a (X x) (X y))
      have hm : X x*X y=X (x+y) := by apply U.ext <;> simp [X]
      rw [hm,mul_c,hx,mul_zero,add_zero] at hh
      exact hh }
  let g : F →+ F := {
    toFun y := (a (Y y)).c
    map_zero' := by change (a 1).c=0; rw [map_one,one_c]
    map_add' x y := by
      have hh := congrArg U.c (map_mul a (Y x) (Y y))
      have hm : Y x*Y y=Y (x+y) := by apply U.ext <;> simp [Y]
      rw [hm,mul_c,hy,zero_mul,add_zero] at hh
      exact hh }
  refine ⟨r,s,σ,f,g,hr,hs,fun u => ?_⟩
  have hu : u = Y u.y*X u.x*central F (Multiplicative.ofAdd u.c) := by
    apply U.ext <;> simp [X,Y,central]
  conv_lhs => rw [hu,map_mul,map_mul,hσ]
  apply U.ext
  · simp [mul_x,central,hy,hax,X,Y]
  · simp [mul_y,central,hx,hay,X,Y]
  · simp only [mul_c,mul_x]
    change (a (Y u.y)).c+(a (X u.x)).c+(a (Y u.y)).x*(a (X u.x)).y+
      c*σ u.c+((a (Y u.y)).x+(a (X u.x)).x)*0 = _
    rw [hy,zero_mul,add_zero,mul_zero,add_zero]
    change g u.y+f u.x+c*σ u.c=r*s*σ u.c+f u.x+g u.y
    rw [hrs]
    ring

end Matrix.PSL3.SmallCompletion
