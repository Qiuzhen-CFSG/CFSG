module
public import Theory.GroupTheory.OrderedRootPresentation.Realization
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Extending an intertwining identity from generators

An equivariance identity for a homomorphism into an ambient group is closed
under actor multiplication and inverses. Checking it on a generating set of
actors therefore suffices. The target group need not carry a separately
constructed invariant action: ambient conjugation provides it.
-/

@[expose] public noncomputable section
namespace Theory.GroupTheory.OrderedRootPresentation
open Subgroup
variable {A K H : Type*} [Group A] [Group K] [Group H]
  (ρ : A →* MulAut K) (s : A →* H) (f : K →* H)

/-- Actors for which the native and ambient actions intertwine. -/
def intertwiningSubgroup : Subgroup A where
  carrier := {a | ∀ v, f (ρ a v) = s a * f v * (s a)⁻¹}
  one_mem' := by intro v; simp
  mul_mem' := by
    intro a b ha hb v
    rw [map_mul,MulAut.mul_apply,ha,hb,map_mul]
    simp only [mul_inv_rev,mul_assoc]
  inv_mem' := by
    intro a ha v
    have h := ha (ρ a⁻¹ v)
    rw [map_inv] at h
    have hv : ρ a ((ρ a)⁻¹ v) = v := by
      rw [← MulAut.mul_apply]
      simp
    rw [hv] at h
    rw [map_inv]
    calc
      f ((ρ a)⁻¹ v) = (s a)⁻¹ * (s a * f ((ρ a)⁻¹ v) * (s a)⁻¹) * s a := by
        simp [mul_assoc]
      _ = (s a)⁻¹ * f v * s a := by rw [← h]
      _ = s a⁻¹ * f v * (s a⁻¹)⁻¹ := by simp

/-- Only the generating actors need to satisfy the intertwining identity. -/
theorem intertwining_of_generators (T : Set A) (hT : closure T = ⊤)
    (h : ∀ a ∈ T, ∀ v, f (ρ a v) = s a * f v * (s a)⁻¹) :
    ∀ a v, f (ρ a v) = s a * f v * (s a)⁻¹ := by
  have hgen : T ⊆ intertwiningSubgroup ρ s f := by
    intro a ha
    exact h a ha
  have he : closure T ≤ intertwiningSubgroup ρ s f :=
    (Subgroup.closure_le _).mpr hgen
  rw [hT] at he
  intro a
  exact he (mem_top a)

end Theory.GroupTheory.OrderedRootPresentation
