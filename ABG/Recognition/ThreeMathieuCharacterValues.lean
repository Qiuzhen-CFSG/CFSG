module
public import ABG.Recognition.ThreeMathieuEvenCharacterValues
public import ABG.Recognition.ThreeMathieuOddCharacterValues

/-!
# Wong's order-7920 character and class analysis

The shared seven-character catalog and the trivial character leave squared
degree sum 512, hence exactly two further irreducibles of degree sixteen and
ten conjugacy classes. The five even classes come from the involution
centralizer. The Sylow eleven-normalizer and the class count give the remaining
classes, with orders three, five, eleven, eleven. Galois invariance, prime-order
trace congruences, and character orthogonality determine the odd values.

This assembly module re-exports the complete class census, the two additional
characters, and the Sylow-five centralizer, conjugacy, and order-twenty
normalizer theorems. The final formula gives the first character on every
element, together with exhaustion of the possible element orders.

Source: Wong (1964), Theorem 6(a), pp.107–108,
DOI 10.1017/S1446788700022771.
-/

namespace ABG
noncomputable section

variable {G : Type*} [Group G] [Finite G] (c : ThreeGlobalDegreeData G)
    [IsSimpleGroup G] (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)

include S hS in
/-- The degree-ten character on every element of the order-7920 branch. -/
public theorem ThreeGlobalDegreeData.first_character_values
    (hG : Nat.card G = 7920) (x : G) :
    c.decomposition.χ 0 x =
      if orderOf x = 1 then 10
      else if orderOf x = 2 ∨ orderOf x = 4 then 2
      else if orderOf x = 3 then 1
      else if orderOf x = 6 ∨ orderOf x = 11 then -1
      else 0 := by
  have hx := c.mathieu_order_exhaustion S hS hG x
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with hx | hx | hx | hx | hx | hx | hx | hx
  · have hx1 : x = 1 := orderOf_eq_one_iff.mp hx
    simpa [hx1] using c.first_character_identity hG
  · simpa [hx] using c.first_character_order_two_or_four S hS x (Or.inl hx)
  · simpa [hx] using c.first_character_order_three S hS hG x hx
  · simpa [hx] using c.first_character_order_two_or_four S hS x (Or.inr hx)
  · simpa [hx] using c.first_character_order_five S hS hG x hx
  · simpa [hx] using c.first_character_order_six S hS x hx
  · simpa [hx] using c.first_character_order_eight S hS x hx
  · simpa [hx] using c.first_character_order_eleven S hS hG x hx

end
end ABG
