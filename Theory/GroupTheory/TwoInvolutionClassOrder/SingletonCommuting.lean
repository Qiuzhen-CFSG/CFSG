module

public import Theory.GroupTheory.TwoInvolutionClassOrder

/-!
# A singleton mixed fiber forces commuting conjugacy classes

The half-order map on mixed pairs is equivariant for simultaneous conjugation.
If its image lies in one conjugacy class and the representative fiber consists
of one commuting pair, every mixed pair is a simultaneous conjugate of that
pair. Hence the two selected conjugacy classes commute elementwise.

This is a direct fiber argument for the singleton case of Thompson counting.
Its application to shearing replaces the centralizer-product cardinality step
in GLS, Volume 4, Chapter 2, Lemma 12.7; see
`refs/KGroup/GLS4/Chapter2.tex`, Lemmas 12.6(c,d) and 12.7.
-/

namespace Theory.GroupTheory.TwoInvolutionClassOrder
variable {G : Type*} [Group G]

/-- A conjugacy-equivariant fiber consisting of one commuting pair forces
all pairs in the two selected classes to commute. -/
public theorem commute_of_singleton_halfOrder_fiber (z v w : G)
    (hc : Commute z v)
    (hsupport : ∀ a b : G, IsConj z a → IsConj v b → IsConj w (halfOrder a b))
    (hsingle : ∀ p : Fiber z v w, p.val = (z, v))
    {a b : G} (ha : IsConj z a) (hb : IsConj v b) : Commute a b := by
  obtain ⟨g, hg⟩ := isConj_iff.mp (hsupport a b ha hb).symm
  let p : Fiber z v w := ⟨(MulAut.conj g a, MulAut.conj g b),
    ha.trans (isConj_iff.mpr ⟨g, rfl⟩),
    hb.trans (isConj_iff.mpr ⟨g, rfl⟩), by
      rw [halfOrder_map]
      exact hg⟩
  have he := hsingle p
  have he1 : MulAut.conj g a = z := congrArg Prod.fst he
  have he2 : MulAut.conj g b = v := congrArg Prod.snd he
  apply (commute_map_iff (MulAut.conj g).injective).mp
  rw [he1, he2]
  exact hc
end Theory.GroupTheory.TwoInvolutionClassOrder
