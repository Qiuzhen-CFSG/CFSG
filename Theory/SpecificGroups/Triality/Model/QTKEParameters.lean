module

public import Theory.SpecificGroups.Triality.Parameters

/-!
# Binary parameters for the triality family

Aschbacher--Smith, Remark A.2.4, includes triality among the rank-two
families in characteristic two. Its parameters are `q = 2^f` with `f > 0`,
including `q = 2`. We specialize the standard prime-power scalar data
and show that these are exactly the parameters whose prime is two.

The module `Triality.Model.QTKE` uses these parameters to specialize the genuine
D4 graph-field carrier. This module does not identify the auxiliary matrix group in
`Triality.Model` with the source family or define a group membership predicate.
-/

@[expose] public section

namespace Triality.Standard

/-- The positive binary parameters used by the QTKE triality family. -/
def binaryParameters (f : ℕ) (hf : 0 < f) : Parameters :=
  ⟨2, f, Nat.prime_two, hf⟩

@[simp] theorem binaryParameters_prime (f : ℕ) (hf : 0 < f) :
    (binaryParameters f hf).prime = 2 := rfl

@[simp] theorem binaryParameters_exponent (f : ℕ) (hf : 0 < f) :
    (binaryParameters f hf).exponent = f := rfl

@[simp] theorem binaryParameters_q (f : ℕ) (hf : 0 < f) :
    (binaryParameters f hf).q = 2 ^ f := rfl

/-- The binary specialization includes every standard parameter of
characteristic two, and only those parameters. -/
theorem exists_binaryParameters_iff (P : Parameters) :
    (∃ (f : ℕ) (hf : 0 < f), binaryParameters f hf = P) ↔ P.prime = 2 := by
  constructor
  · rintro ⟨f, hf, rfl⟩
    rfl
  · intro hp
    rcases P with ⟨p, f, hpprime, hf⟩
    change p = 2 at hp
    subst p
    exact ⟨f, hf, rfl⟩

end Triality.Standard
