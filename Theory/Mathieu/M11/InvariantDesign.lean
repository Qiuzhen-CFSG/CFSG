module

public import Theory.Mathieu.M11.SharpAction
public import Theory.Mathieu.M11.SharpLocalOrbits
public import Theory.GroupTheory.SteinerSystemOrbit

/-!
# An invariant Witt design from a sharp degree-eleven action

Every faithful sharply four-transitive action on eleven points preserves a
Steiner system `S(4, 5, 11)`.

The setwise stabilizer of a four-set has complementary orbits of sizes one and
six. Adjoin its fixed point to the four-set and take the orbit of this
five-set as blocks. If two such blocks contained the same four-set, local
transitivity and four-transitivity would force all five-sets into that orbit.
This contradicts the cardinal obstruction: 462 does not divide 7920. The
general orbit construction therefore supplies the full unique-extension
property and invariance under every action permutation.

Source: Jordan's degree-eleven theorem, cited in Wong (1964), p. 108, and
Hall, *The Theory of Groups*, Theorem 5.8.1.
-/

namespace Sporadic.Mathieu

/-- A faithful sharply four-transitive degree-eleven action preserves a Witt design. -/
public theorem sharpFour_degreeEleven_exists_invariantDesign
    {G : Type*} [Group G] [Finite G] [MulAction G (Fin 11)]
    [FaithfulSMul G (Fin 11)]
    (h : Theory.GroupTheory.MulAction.IsSharplyMultiplyPretransitive G (Fin 11) 4) :
    ∃ D : Theory.GroupTheory.SteinerSystem (Fin 11) 4 5,
      ∀ g : G, MulAction.toPerm g ∈ D.aut := by
  classical
  let S : Finset (Fin 11) := Finset.univ.map (Fin.castLEEmb (by decide : 4 ≤ 11))
  have hS : S.card = 4 := by simp [S]
  obtain ⟨p, hp, _hfix, hlocal⟩ :=
    h.exists_fixed_point_and_transitive_fourSet_complement S hS
  exact Theory.GroupTheory.SteinerSystem.exists_invariant_of_two_extension_orbits
    4 h.isMultiplyPretransitive (sharpFour_degreeEleven_not_fiveHomogeneous h)
    S p hS hp hlocal

end Sporadic.Mathieu
