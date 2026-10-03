module

public import Theory.GroupTheory.PGroup.SymplecticType
public import Theory.GroupTheory.SpecificGroups.GeneralizedQuaternionAut
public import Theory.GroupTheory.SpecificGroups.DihedralAut
public import Theory.GroupTheory.SemidihedralAut

/-!
# Automorphisms of large binary Hall factors

A binary Hall factor of order at least sixteen has a two-group of
automorphisms. For cyclic groups this is the units calculation; for the
three maximal-class families it follows by restricting automorphisms to
their characteristic cyclic subgroup of index two. The size condition
excludes the quaternion and dihedral exceptions of order at most eight.

This is the tail-factor calculation used in Janko–Thompson, Math. Z. 113
(1970), §4, p.392. It does not assert that a displayed Hall factor is
characteristic in a larger central product.
-/

/-- A binary Hall two-group of order at least sixteen has no odd-order
automorphisms. -/
public theorem IsBinaryHallFactor.isPGroup_mulAut_of_sixteen_le
    {D : Type*} [Group D] [Finite D] (hD : IsBinaryHallFactor D)
    (hP : IsPGroup 2 D) (hcard : 16 ≤ Nat.card D) :
    IsPGroup 2 (MulAut D) := by
  rcases hD with hcyc | ⟨n, -, ⟨e⟩⟩ | ⟨m, ⟨e⟩⟩ |
    ⟨n, hn, hc, a, b, ha, hb, hr, hg⟩
  · let : IsCyclic D := hcyc
    exact hP.mulAut_of_isCyclic_two
  · have hc : Nat.card D = 4 * 2 ^ (n - 2) := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    exact (QuaternionGroup.isPGroup_mulAut_of_two_lt (by omega)
      (hP.of_equiv e)).of_equiv (MulAut.congr e.symm)
  · have hc : Nat.card D = 2 * m :=
      (Nat.card_congr e.toEquiv).trans DihedralGroup.nat_card
    exact (DihedralGroup.isPGroup_mulAut_of_two_lt (by omega)
      (hP.of_equiv e)).of_equiv (MulAut.congr e.symm)
  · exact Semidihedral.isPGroup_mulAut hn hc a b ha hb hr hg
