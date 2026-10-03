module

public import ABG.Recognition.ThreeLinearPlane
public import Theory.Combinatorics.ProjectivePlaneThreeRecognition
public import Theory.SpecificGroups.LinearCoefficientEquiv

/-!
# Recognition of Wong's order-5616 branch

A finite simple group with a semidihedral Sylow two-subgroup of order sixteen,
involution centralizers isomorphic to `GL₂(3)`, and order 5616 is isomorphic
to the concrete projective special linear group `PSL₃(3)`.

Wong's character package constructs the index-thirteen subgroup and the
projective plane whose points are four-line fixed sets of order-three elements.
The faithful action on its lines gives an embedding into its full collineation
group. Incidence coordinates identify this group with the matrix model over
`ZMod 3`; only then does equality of orders prove surjectivity. Entrywise
transport along `GF(3) ≃ ZMod 3` identifies this model with `ABG.PSL3 3 1`.

Source: W. J. Wong, *On finite groups whose 2-Sylow subgroups have cyclic
subgroups of index 2* (1964), Theorem 6(b), pp.108–111,
DOI: 10.1017/S1446788700022771.
-/

namespace ABG

/-- Wong's order-5616 branch is the actual projective special linear group
over the three-element Galois field. -/
public theorem nonempty_mulEquiv_PSL3_of_card_eq_5616
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)
    (hcard : Nat.card S = 16)
    (hC : ∀ t : G, orderOf t = 2 →
      Subgroup.centralizer ({t} : Set G) ≃* GL2 3 1)
    (hG : Nat.card G = 5616) :
    Nonempty (G ≃* PSL3 3 1) := by
  obtain ⟨c, hplane, hfaithful, hcollineation, _, _, hfour, _⟩ :=
    exists_threeLinearPlane S hS hcard hC hG
  let := Classical.choice hplane
  let := hfaithful
  let := hcollineation
  obtain ⟨e⟩ := Configuration.PlaneThree.nonempty_mulEquiv_PSL G
    (P := ThreeLinearPlane.Point G (G ⧸ c.subgroup))
    (L := ThreeLinearPlane.Line G (G ⧸ c.subgroup)) hfour hG
  exact ⟨e.trans (Matrix.ProjectiveSpecialLinearGroup.ringEquiv
    (GaloisField.equivZmodP 3).toRingEquiv.symm)⟩

/-- The order-5616 alternative in Wong's theorem satisfies the ABG linear
recognition predicate, with characteristic three and extension degree one. -/
public theorem isPSL3_of_card_eq_5616
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)
    (hcard : Nat.card S = 16)
    (hC : ∀ t : G, orderOf t = 2 →
      Subgroup.centralizer ({t} : Set G) ≃* GL2 3 1)
    (hG : Nat.card G = 5616) : IsPSL3 G 3 :=
  ⟨3, 1, by decide, by decide, by decide,
    nonempty_mulEquiv_PSL3_of_card_eq_5616 S hS hcard hC hG⟩

end ABG
