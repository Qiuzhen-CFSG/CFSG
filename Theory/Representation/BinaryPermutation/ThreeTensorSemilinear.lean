module

public import Theory.Representation.BinaryPermutation.ThreeTensorDisplacement
public import Theory.LinearAlgebra.BinarySemilinearDisplacement

/-!
# Displacement in a degree-two semilinear tensor model

On tensoring a faithful semilinear module of binary dimension at least four
with the natural S₃-module, every nonidentity actor moves at least four
binary dimensions. A nontrivial S₃ component gives the dimension bound
directly; otherwise the minimum first-factor displacement doubles.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, the natural
L₂(4) tensor exclusion in 14.4.6(a), printed p.1008. Identification of the
full natural-module action as semilinear is a separate model theorem.
-/

public section
namespace BinaryPermutation.ThreeTensor
open Module Representation.BinaryOffender.NaturalTensor
variable {F W D : Type*} [Field F] [Algebra (ZMod 2) F]
  [AddCommGroup W] [Module F W] [Module (ZMod 2) W] [IsScalarTower (ZMod 2) F W]
  [Module.Finite (ZMod 2) W] [Group D]

/-- The natural tensor branch has no nonidentity actor of binary moved rank at most two. -/
theorem four_le_displacement_of_semilinear
    (hdegree : finrank (ZMod 2) F = 2) (hdim : 4 ≤ finrank (ZMod 2) W)
    (ρ : Representation (ZMod 2) D W) (hfaith : Function.Injective ρ)
    (hsemi : ∀ g, ∃ σ : F →+* F, ∀ a v, ρ g (a • v) = σ a • ρ g v)
    (g : D × Equiv.Perm (Fin 3)) (hg : g ≠ 1) :
    4 ≤ finrank (ZMod 2) (LinearMap.range (action ρ g - LinearMap.id)) := by
  by_cases hs : g.2 = 1
  · have he : g = (g.1, 1) := Prod.ext rfl hs
    have hfirst : ρ g.1 ≠ 1 := by
      intro h
      apply hg
      exact Prod.ext (hfaith (h.trans (map_one ρ).symm)) hs
    obtain ⟨σ, hσ⟩ := hsemi g.1
    have hb := two_le_semilinear_displacement hdegree hdim (ρ g.1) hfirst σ hσ
    rw [he, displacement_first]
    omega
  · exact hdim.trans (dimension_le_displacement ρ g hs)
end BinaryPermutation.ThreeTensor
