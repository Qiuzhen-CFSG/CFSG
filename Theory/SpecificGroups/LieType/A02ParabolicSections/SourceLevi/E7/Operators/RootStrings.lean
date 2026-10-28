module

public import Theory.SpecificGroups.LieType.A02ParabolicSections.SourceLevi.E7.Operators.Indexing

/-!
# Unit coefficients in the simply laced E7 root strings

All native E7 roots have squared length two. If the sum of two roots is a
root, the squared length of their difference is six, so the backward string
is empty. This gives the coefficient one in every nonzero off-diagonal root
entry of a simple Geck operator.
-/

@[expose] public section
open Theory.AlgebraicGroup.StandardRootSystem
namespace Theory.SpecificGroups.LieType.SourceLevi.E7.Operators
noncomputable section
open scoped Classical
local instance : InvolutiveNeg typeE7Roots := typeE7RootPairing.indexNeg

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

theorem chainBotCoeff_of_sum {i j k : typeE7Roots}
    (h : typeE7RootPairing.root k = typeE7RootPairing.root i + typeE7RootPairing.root j) :
    typeE7RootPairing.chainBotCoeff i j = 0 := by
  apply typeE7RootPairing.chainBotCoeff_eq_zero_iff.mpr
  right
  rintro ⟨s, hs⟩
  have hk : k.val = i.val + j.val := congrArg Subtype.val h
  have hs' : s.val = j.val - i.val := congrArg Subtype.val hs
  have hkn := typeE7Root_dot_self k
  have hsn := typeE7Root_dot_self s
  rw [hk, norm_add, typeE7Root_dot_self, typeE7Root_dot_self] at hkn
  rw [hs', norm_sub, typeE7Root_dot_self, typeE7Root_dot_self, dot_comm j.val i.val] at hsn
  linarith

end
end Theory.SpecificGroups.LieType.SourceLevi.E7.Operators
