module

public import Theory.SpecificGroups.PSL3.OuterSolvable.OddPrimeCoverage.RootRigidity
public import Theory.SpecificGroups.PSL3.OuterSolvable.OddPrimeCoverage.UnipotentGeometry
public import Theory.SpecificGroups.PSL3.OuterSolvable.OddPrimeCoverage.RootOrientation.Torus
public import Theory.SpecificGroups.PSL3.OuterSolvable.OddPrimeCoverage.RootOrientation.Centralizers

/-!
# Orienting roots after an opposite unipotent pair is fixed

Preserving the upper and lower unitriangular subgroups preserves their
Borel normalizers and hence the diagonal torus. Its three nonidentity
involutions recover the three pairs of opposite roots by centralizers.
The central highest root fixes one label, leaving the identity permutation
or the explicit opposition graph automorphism. This proves root preservation
after the required correction, including the prime p = 3.

The opposite-pair hypothesis remains explicit: the parent coverage argument
must establish it. Simplicity and nonsolvability are inherited from that
consumer; the coordinate argument itself needs neither.
Source: GLS3, Theorem 2.5.12(a) and §2.7,
`refs/KGroup/GLS3/chapter2.tex`, lines 1111–1115.
-/

public section

open scoped MatrixGroups
namespace Matrix.PSL3.OuterSolvable.OddPrimeCoverage
variable {F : Type*} [Field F] [Finite F]

/-- An automorphism preserving the two opposite unitriangular subgroups fixes
all six coordinate roots after at most the explicit A₂ diagram symmetry. -/
theorem exists_oppositionGraph_preserves_roots [IsSimpleGroup PSL(3,F)]
    (_hns : ¬ Group.IsSolvable PSL(3,F)) (p : ℕ) (hp : p.Prime) (hodd : Odd p)
    (hF : Nat.card F = p) (α : MulAut PSL(3,F)) (hα : PreservesUnipotentPair F α) :
    ∃ ε : Fin 2, PreservesRootGroups ((oppositionGraph F ^ (ε : ℕ))⁻¹ * α) := by
  have h2 : (2 : F) ≠ 0 := by
    let := Fintype.ofFinite F
    intro hz
    have hc : ringChar F = 2 := CharP.ringChar_of_prime_eq_zero Nat.prime_two hz
    have he := FiniteField.even_card_iff_char_two.mp hc
    rw [← Nat.card_eq_fintype_card, hF] at he
    have ho := Nat.odd_iff.mp hodd
    omega
  exact exists_oppositionGraph_of_sign_geometry α hα
    (exists_sign_permutation hp hF h2 α hα)
    (upper_inf_centralizer_sign h2) (lower_inf_centralizer_sign h2)
    positiveRoot_central_iff

end Matrix.PSL3.OuterSolvable.OddPrimeCoverage
