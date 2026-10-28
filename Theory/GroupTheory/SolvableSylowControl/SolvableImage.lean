module
public import Theory.GroupTheory.SolvableSylowControl
public import Theory.GroupTheory.SolvableRadical.SolvableKernel

/-!
# Solvable Sylow control descends through solvable kernels

A solvable subgroup downstairs has solvable full preimage. Lift its supplied
Sylow along the actual surjection, apply control upstairs, and map its
normalizer back down. No choice of a complement or injectivity is required.

Source application: the natural-layer image on V_M in Aschbacher--Smith
11.2.1, printed pp.766--767.
-/

public section
open Subgroup
namespace Theory.GroupTheory.SolvableSylowControl
variable {p : ℕ} [Fact p.Prime]
variable {G H : Type*} [Group G] [Finite G] [Group H]

/-- Solvable Sylow control passes to an image with solvable action kernel. -/
theorem of_surjective_solvable_kernel (f : G →* H) (hf : Function.Surjective f)
    [Group.IsSolvable f.ker] (h : SolvableSylowControl p G) :
    SolvableSylowControl p H := by
  intro S A hA hSA
  let := hA
  obtain ⟨P, hP⟩ := Sylow.mapSurjective_surjective hf p S
  let := isSolvable_comap_of_solvable_ker f A
  have hPA : (P : Subgroup G) ≤ A.comap f := by
    intro x hx
    exact hSA (show f x ∈ (S : Subgroup H) by
      rw [← hP]
      exact mem_map_of_mem f hx)
  have hn := h P (A.comap f) inferInstance hPA
  have hm := (map_mono hn).trans ((P : Subgroup G).le_normalizer_map f)
  rw [map_comap_eq_self_of_surjective hf] at hm
  change A ≤ normalizer ((P.mapSurjective hf : Sylow p H) : Set H) at hm
  rwa [hP] at hm
end Theory.GroupTheory.SolvableSylowControl
