module

public import Theory.AlgebraicGroup.Borel.ElementCoverage.FiniteFiberDensity.OneFiber
public import Theory.AlgebraicGroup.Borel.ElementCoverage.FiniteFiberDensity.AffineConjugation

/-!
# Density of the union of conjugates from a finite fixed-point fibre

Let `G` and `H` be connected algebraic groups, with `H` a closed subgroup of
`G`. If some `h ∈ H` fixes only finitely many points of `G/H`, then the union
of conjugates of `H` is dense in `G`.

We use the affine conjugation morphism `G × H → G`. Its source is irreducible
of dimension `dim G + dim H`. The fibre over `h` is nonempty, and its
irreducible closed subsets have dimension at most `dim H`, because the finite
fixed-point hypothesis covers the fibre by finitely many coset slices.
The one-fibre height inequality then proves dominance.

Source: Borel, *Linear Algebraic Groups*, §11.9(2),
`refs/KGroup/Bor1/Chapter4.tex`, lines 124–161. This is the affine alternative
to the incidence-variety argument; no solvability, completeness, separability,
or dimension certificate is assumed.
-/

namespace Theory.AlgebraicGroup.BorelElementCoverage

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

/-- The finite fixed-point hypothesis of Borel §11.9(2) implies density of
the union of conjugates of a connected closed subgroup. -/
public theorem dense_conjugacySaturation_of_finite_fixedPoints
    (hG : Variety.IsConnected G) (H : ClosedSubgroup G)
    (hH : _root_.IsConnected (H : Set (Variety.Point G)))
    (h : Variety.Point G) (hh : h ∈ H.toSubgroup)
    (hfinite : Set.Finite {q : Bor1.borelHomogeneousSpace H | h • q = q}) :
    Dense (conjugacySaturation H) := by
  have hHi : IsIrreducible (Set.univ : Set (Variety.Point H.carrierVariety)) := by
    apply connectedAlgebraicGroup_irreducible
    let e := Variety.closedSubvarietyPointHomeomorph H.isZariskiClosed
    let : ConnectedSpace (H : Set (Variety.Point G)) := Subtype.connectedSpace hH
    let : ConnectedSpace (Variety.Point H.carrierVariety) :=
      e.connectedSpace_iff.mpr inferInstance
    exact connectedSpace_iff_univ.mp inferInstance
  have hGi := connectedAlgebraicGroup_irreducible G hG
  have hVi : IsIrreducible
      (Set.univ : Set (Variety.Point (Variety.prod G H.carrierVariety))) := by
    simpa only [Variety.prodSet, Set.mem_univ, and_self, Set.ofPred_true] using
      prodSet_irreducible_of_irreducible hGi hHi
  let a : Variety.Point H.carrierVariety := H.pointEquiv.symm ⟨h, hh⟩
  let z := (Variety.prodPointEquiv G H.carrierVariety).symm (1, a)
  have hz : (subgroupConjugation H).toFun z = h := by
    rw [subgroupConjugation_apply]
    change 1 * H.inclusion.onPoints a * (1 : Variety.Point G)⁻¹ = h
    simp only [one_mul, inv_one, mul_one]
    change (H.pointEquiv (H.pointEquiv.symm _)).val = _
    simp only [Equiv.apply_symm_apply]
  rw [← subgroupConjugation_range H]
  apply denseRange_of_one_fiber_dimension_le (subgroupConjugation H) hVi hGi
    (Variety.dimension H.carrierVariety) (variety_dimension_lt_aleph0 _)
    (dimension_product_additive G H.carrierVariety) z
  intro S hS hSi hSf
  apply subgroupConjugation_fiber_dimension_le H hHi h hfinite S hS hSi
  simpa only [hz] using hSf

end Theory.AlgebraicGroup.BorelElementCoverage
