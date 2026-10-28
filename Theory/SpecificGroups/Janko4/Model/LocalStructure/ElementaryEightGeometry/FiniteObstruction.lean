module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.MaskParity

/-!
# The incompatible marked lift equations

The two involutivity conditions, pair-centralization equation, and mutual
commutation equation contradict the certified action parities. This is the
finite-coordinate part of KW (1988), Proposition 2.3.4(ii); native transport
is supplied separately.
-/

public section
namespace Janko4.LocalStructure.ElementaryEightGeometry
open Cardinality.QuotientCount.Image SylowCore

/-- The two primed-(b) lifts cannot be commuting involutions centralizing
 the Figure 1(c) pair twist with kernel mask four. -/
theorem no_bbb_pair_masks (m n : Fin 2048)
    (hm : maskImage (actionRows 0 1) m.val = m.val)
    (hn : maskImage (actionRows 0 2) n.val = n.val)
    (hp : maskImage pairActionRows n.val ^^^ n.val = 1129)
    (hc : maskImage (actionRows 0 2) m.val ^^^ m.val =
      maskImage (actionRows 0 1) n.val ^^^ n.val) : False := by
  have h1 := first_parity m
  have h2 := second_parity n
  rw [hm, Nat.xor_self] at h1
  simp only [Nat.zero_testBit, Bool.false_xor] at h1
  rw [hn, Nat.xor_self, hp] at h2
  rw [hc] at h1
  rw [h1] at h2
  exact (by decide +kernel : ¬ (Nat.testBit 0 4 ^^ Nat.testBit 1129 0 ^^ Nat.testBit 1129 1 ^^ false) = false) h2

end Janko4.LocalStructure.ElementaryEightGeometry
