module

public import Theory.SpecificGroups.PSL3.SmallCompletion.UnipotentAutomorphismForm

/-!
# The full torus forces Frobenius central corrections

For an ordered root-plane automorphism normalizing the simultaneous-scaling
torus, the two additive central corrections are scalar multiples of the
square of the recovered field automorphism. This retains the whole torus
condition, rather than assuming a restriction on a Sylow subgroup alone.
-/

public noncomputable section
namespace Matrix.PSL3.SmallCompletion
open Matrix.PSL3Even.UnipotentGeometry
variable {F : Type*} [Field F] [Finite F]

/-- Exact normal form after the original torus has been aligned. -/
theorem torus_normalized_root_plane_automorphism_form (a : MulAut (U F))
    (h₁ : ∀ u ∈ V₁ F, a u ∈ V₁ F)
    (h₂ : ∀ u ∈ V₂ F, a u ∈ V₂ F)
    (ht : ∀ t : Fˣ, ∃ s : Fˣ, ∀ u : U F,
      a ⟨t*u.x,t*u.y,(t:F)^2*u.c⟩ =
        ⟨s*(a u).x,s*(a u).y,(s:F)^2*(a u).c⟩) :
    ∃ (r s k l : F) (σ : F ≃+* F), r ≠ 0 ∧ s ≠ 0 ∧
      ∀ u : U F,
        a u = ⟨r*σ u.x,s*σ u.y,r*s*σ u.c+k*(σ u.x)^2+l*(σ u.y)^2⟩ := by
  obtain ⟨r,s,σ,f,g,hr,hs,ha⟩ := ordered_root_plane_automorphism_form a h₁ h₂
  have hfg (t : Fˣ) : f (t:F) = f 1*(σ (t:F))^2 ∧
      g (t:F) = g 1*(σ (t:F))^2 := by
    obtain ⟨d,hd⟩ := ht t
    have hx := hd (⟨1,0,0⟩ : U F)
    have hy := hd (⟨0,1,0⟩ : U F)
    rw [ha,ha] at hx hy
    have hdσ : σ (t:F) = (d:F) := by
      apply mul_left_cancel₀ hr
      simpa only [mul_one,mul_zero,map_one,map_zero,zero_add,add_zero,mul_comm (d:F)] using
        congrArg U.x hx
    have hf := congrArg U.c hx
    have hg := congrArg U.c hy
    simpa [hdσ,mul_comm] using And.intro hf hg
  have hf (x : F) : f x = f 1*(σ x)^2 := by
    by_cases hx : x=0
    · simp [hx]
    · exact (hfg (Units.mk0 x hx)).1
  have hg (x : F) : g x = g 1*(σ x)^2 := by
    by_cases hx : x=0
    · simp [hx]
    · exact (hfg (Units.mk0 x hx)).2
  exact ⟨r,s,f 1,g 1,σ,hr,hs,fun u => by rw [ha,hf,hg]⟩

end Matrix.PSL3.SmallCompletion
