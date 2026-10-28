module

public import Theory.Representation.G2BinaryHyperplanes

/-!
# Large fixed subspaces in the binary natural G₂ module

The hyperplane fixer argument only uses that the fixed subspace has codimension
at most one.  This extension records the form needed when a subspace of the
seven-dimensional orthogonal cover projects to a five- or six-dimensional
subspace of the natural six-space.
-/

public section
open Module Submodule LinearMap
namespace Atlas.G2.Natural.BinaryNondegeneratePlane

lemma pointwise_large_subspace_trivial (U : Submodule K W)
    (hU : 5 ≤ finrank K U) (g : Model K)
    (hfix : ∀ v ∈ U, rho g v = v) : g = 1 := by
  let e := LinearMap.GeneralLinearGroup.toLinearEquiv (rho.asGroupHom g)
  have he : ∀ v ∈ U, e v = v := hfix
  have hquot : finrank K (W ⧸ U) ≤ 1 := by
    have hdim := U.finrank_quotient_add_finrank
    rw [Module.finrank_fin_fun] at hdim
    omega
  have hsq := BinaryFourFixedSpace.pointwiseFixer_sq U hquot ⟨e, he⟩
  have hg2 : g * g = 1 := by
    apply rho_injective
    apply LinearMap.ext
    intro v
    have hh := congrArg (fun a : BinaryFourFixedSpace.pointwiseFixer U => a.val v) hsq
    change rho g (rho g v) = v at hh
    simpa only [map_mul, Module.End.mul_apply, map_one, Module.End.one_apply] using hh
  by_contra hne
  have hr := InvolutionRank.two_le_operatorFixedCodim_of_involution g hne hg2
  have heq := Representation.BinaryOffender.NaturalTensor.operatorFixedCodim_eq_of_equiv
    (Natural.action K g) (rho g) (Restricted.NaturalCoordinates.equiv K)
    (fun v => LinearMap.congr_fun
      ((Restricted.NaturalCoordinates.repEquiv K).isIntertwining' g) v)
  rw [heq] at hr
  have hker : U ≤ (rho g - 1).ker := by
    intro v hv
    change rho g v - v = 0
    exact sub_eq_zero.mpr (hfix v hv)
  have hd := Submodule.finrank_mono hker
  have hnull := (rho g - 1).finrank_range_add_finrank_ker
  change 2 ≤ finrank K (rho g - 1).range at hr
  change finrank K (rho g - 1).range + finrank K (rho g - 1).ker = finrank K W at hnull
  change finrank K U ≤ finrank K (rho g - 1).ker at hd
  rw [Module.finrank_fin_fun] at hnull
  omega

end Atlas.G2.Natural.BinaryNondegeneratePlane
