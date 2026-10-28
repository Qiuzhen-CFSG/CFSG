module

public import Theory.SpecificGroups.LieType.A02ParabolicSections.SourceLevi.E6.Operators.Indexing

/-!
# Unit coefficients in the simply laced E₆ root strings

All native E₆ roots have squared length two. If the sum of two roots is a
root, the squared length of their difference is six, so the backward string
is empty. This gives the coefficient one in every nonzero off-diagonal root
entry of a simple Geck operator.
-/

@[expose] public section
open Theory.AlgebraicGroup.StandardRootSystem
namespace Theory.SpecificGroups.LieType.SourceLevi.E6.Operators
noncomputable section
open scoped Classical
local instance : InvolutiveNeg typeE6Roots := typeE6RootPairing.indexNeg

private theorem norm_add (x y : Vec 8) :
    dot (x + y) (x + y) = dot x x + 2 * dot x y + dot y y := by
  simp only [dot, Pi.add_apply]
  simp_rw [add_mul, mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp_rw [mul_comm (y _)]
  ring

private theorem norm_sub (x y : Vec 8) :
    dot (x - y) (x - y) = dot x x - 2 * dot x y + dot y y := by
  simp only [dot, Pi.sub_apply]
  simp_rw [sub_mul, mul_sub]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  simp_rw [mul_comm (y _)]
  ring

theorem chainBotCoeff_of_sum {i j k : typeE6Roots}
    (h : typeE6RootPairing.root k = typeE6RootPairing.root i + typeE6RootPairing.root j) :
    typeE6RootPairing.chainBotCoeff i j = 0 := by
  apply typeE6RootPairing.chainBotCoeff_eq_zero_iff.mpr
  right
  rintro ⟨s, hs⟩
  have hk : k.val = i.val + j.val := congrArg Subtype.val h
  have hs' : s.val = j.val - i.val := congrArg Subtype.val hs
  have hkn := typeE6Root_dot_self k
  have hsn := typeE6Root_dot_self s
  rw [hk, norm_add, typeE6Root_dot_self, typeE6Root_dot_self] at hkn
  rw [hs', norm_sub, typeE6Root_dot_self, typeE6Root_dot_self, dot_comm j.val i.val] at hsn
  linarith

end
end Theory.SpecificGroups.LieType.SourceLevi.E6.Operators
