module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.Scalar
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.Marking.ScalarAction

/-!
# The scalar involution has the prescribed Leech marking

The explicit signed Golay permutation in `Marking.ScalarAction` conjugates
the lift of the icosian unit i to the literal `markedLift`. Projecting gives
a marked involution in the actual scalar A₅. Its unique involution class then
conjugates the specified double transposition (01)(23) to that element.
Thus this proof uses an equality of concrete Leech isometries and the actual
scalar embedding, including its inverse right-multiplication convention.

This discharges the marking premise of `nonempty_shortFrame_of_scalar_seed`
in `LocalGenerators.Short`; that parent retains the independent local A₅
construction and final short-frame assembly.

Source: Aschbacher, *Sporadic Groups* (1994), root-four definitions p.269 and
Lemma 49.5, pp.283–284. Lemma 46.9, p.254 supplies the source order-four lift
property; the conjugacy here is proved by the explicit coordinate calculation.
-/

public section

open Atlas.Algebra Atlas.Conway
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators

/-- Conjugacy to the prescribed signed-permutation marking in the actual Co₁ model. -/
theorem scalarInvolution_isConj_marked : IsConj scalarInvolution markedInvolution := by
  let q : IcosianScalarProjectiveModel := QuotientGroup.mk Marking.unitI
  let s : alternatingGroup (Fin 5) := icosianScalarProjectiveAlternating q
  have he : scalarFive s = leechCentralProjection (icosianScalarsToCo0 Marking.unitI) := by
    change icosianScalarProjectiveToCo1
      (icosianScalarProjectiveAlternating.symm (icosianScalarProjectiveAlternating q)) = _
    rw [MulEquiv.symm_apply_apply]
    rfl
  have hc : IsConj (scalarFive s) markedInvolution := by
    rw [he]
    exact Marking.scalarI_projection_isConj_marked
  have ho : orderOf (scalarFive s) = orderOf markedInvolution := by
    obtain ⟨g, hg⟩ := hc
    exact SemiconjBy.orderOf_eq (↑g) hg
  have hs : orderOf s = 2 := by
    rw [← orderOf_injective scalarFive scalarFive_injective, ho, markedInvolution_order]
  exact (scalarFive_involution_isConj s hs).symm.trans hc

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators
