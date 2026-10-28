module
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.FixedSingularPlane
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.SingularPairCubicFixed

/-! A nontrivial cubic commuting with a swapping actor in O₄⁺(2) has
no nonzero fixed vector. The two plane actions are conjugate nontrivial
three-cycles. This is the cubic calculation in source 14.3.19. -/

public section
open Subgroup
namespace BinaryFourPlus
private instance : DecidableEq Wreath :=
  (RegularWreathProduct.equivProd (Equiv.Perm (Fin 3)) C2).injective.decidableEq
private instance : Fintype Wreath := Fintype.ofEquiv _
  (RegularWreathProduct.equivProd (Equiv.Perm (Fin 3)) C2).symm

private theorem plane_cubic_fixed (p:Equiv.Perm (Fin 3))
    (hp:p^3=1) (hn:p≠1) (v:Plane) (hv:planeLinear p v=v) : v=0 := by
  have hf:∀p:Equiv.Perm (Fin 3),p^3=1→p≠1→∀i,p i≠i := by decide +kernel
  have hc:∀v:Plane,v=0∨∃i,v=nonzeroVector i := by decide +kernel
  rcases hc v with h|⟨i,rfl⟩
  · exact h
  · rw [planeLinear_nonzeroVector] at hv
    exact (hf p hp hn i (nonzeroVector_injective hv)).elim

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem centralizer_cubic_coordinates : ∀a b:Wreath,
    a.right≠1→b^3=1→b≠1→a*b=b*a→
    b.right=1 ∧ ∀i:C2,(b.left i)^3=1 ∧ b.left i≠1 := by
  decide +kernel

theorem swapping_centralizer_cubic_fixed_free (a b:Wreath)
    (ha:a.right≠1) (hb:b^3=1) (hn:b≠1) (hc:Commute a b)
    (v:V) (hv:(wreathToIsometry b).val v=v) : v=0 := by
  obtain ⟨hr,hp⟩:=centralizer_cubic_coordinates a b ha hb hn hc.eq
  rw [wreathToIsometry_apply,if_pos hr] at hv
  apply Prod.ext
  · exact plane_cubic_fixed _ (hp 1).1 (hp 1).2 v.1 (congrArg Prod.fst hv)
  · exact plane_cubic_fixed _ (hp swapIndex).1 (hp swapIndex).2 v.2 (congrArg Prod.snd hv)
end BinaryFourPlus
