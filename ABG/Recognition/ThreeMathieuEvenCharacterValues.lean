module
public import ABG.Recognition.ThreeMathieuCharacterCount
public import ABG.Recognition.ThreeMathieuEvenClasses

/-!
# Wong's first character at the identity and on even classes

This module records the order-7920 consequences of the common character
catalog.  Values on the roots of the distinguished involution are transported
from the actual `GL₂(3)` table; the identity and involution values are then
identified with the first degree and the involution vector.

Source: Wong (1964), Theorem 6(a), pp.107–108,
DOI 10.1017/S1446788700022771.
-/

namespace ABG
open BenderGlauberman Matrix.GeneralLinearGroup
open scoped BigOperators
noncomputable section

variable {G : Type*} [Group G] [Finite G] (c : ThreeGlobalDegreeData G)

/-- The value of Wong's first character at the identity in the order-7920
branch. -/
public theorem ThreeGlobalDegreeData.first_character_identity
    (hG : Nat.card G = 7920) : c.decomposition.χ 0 1 = 10 := by
  have h := c.decomposition.degree_eq 0
  rw [c.mathieu_degrees hG] at h
  norm_num [Matrix.cons_val] at h ⊢
  exact h

/-- The first character has value two at the distinguished involution. -/
public theorem ThreeGlobalDegreeData.first_character_involution
    [IsSimpleGroup G] {S : Sylow 2 G} (hS : Stellmacher.IsSemidihedralGroup S) :
    c.decomposition.χ 0 c.involution = 2 := by
  have h := threeInduced_involution_vector S hS c.involution c.order_involution
    c.centralizerEquiv c.decomposition 0
  simpa using h

/-- The values of the first character on all five local root classes.  The
indices are the concrete `GL₂(3)` class representatives; their orders are
`2,4,6,8,8` respectively. -/
public theorem ThreeGlobalDegreeData.first_character_root_values
    (j : Fin 8) (hj : j = 1 ∨ j = 2 ∨ j = 4 ∨ j = 6 ∨ j = 7) :
    c.decomposition.χ 0
      ((threeCentralizerEquiv c.involution c.centralizerEquiv).symm
        (threeClassRepr j)) = (![0,2,2,0,-1,0,0,0] j : ℂ) :=
  c.first_root_class_values j hj

public theorem ThreeGlobalDegreeData.first_character_conjugacy_invariant
    {x y : G} (hxy : IsConj x y) :
    c.decomposition.χ 0 x = c.decomposition.χ 0 y := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hxy
  have hclass := irreducibleCharacter_isClassFunction (c.decomposition.irreducible 0) x g
  rw [hg] at hclass
  exact hclass.symm

/-- Value two on the order-two and order-four classes. -/
public theorem ThreeGlobalDegreeData.first_character_order_two_or_four
    [IsSimpleGroup G] (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)
    (x : G) (hx : orderOf x = 2 ∨ orderOf x = 4) : c.decomposition.χ 0 x = 2 := by
  have heven : 2 ∣ orderOf x := by rcases hx with h | h <;> norm_num [h]
  have h := c.first_character_even_values S hS x heven
  rcases hx with hx | hx <;> simpa [hx] using h

/-- Value minus one on the order-six class. -/
public theorem ThreeGlobalDegreeData.first_character_order_six
    [IsSimpleGroup G] (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)
    (x : G) (hx : orderOf x = 6) : c.decomposition.χ 0 x = -1 := by
  simpa [hx] using c.first_character_even_values S hS x (by rw [hx]; norm_num)

/-- The first character vanishes on both order-eight classes. -/
public theorem ThreeGlobalDegreeData.first_character_order_eight
    [IsSimpleGroup G] (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)
    (x : G) (hx : orderOf x = 8) : c.decomposition.χ 0 x = 0 := by
  simpa [hx] using c.first_character_even_values S hS x (by rw [hx]; norm_num)


end
end ABG
