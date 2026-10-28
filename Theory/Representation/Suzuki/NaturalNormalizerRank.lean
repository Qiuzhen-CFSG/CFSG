module
public import Theory.Representation.BinaryScalarCommutant
public import Theory.Representation.Suzuki.NaturalCentralizer
public import Theory.SpecificGroups.Suzuki.TwoRank

/-!
# The full binary normalizer of the natural Suzuki module

The natural action is faithful and its additive commutant is scalar.
Thus elementary two-subgroups of its full binary linear normalizer embed
in Aut(Sz(2^(2m+1))), whose two-rank is at most 2m+1.
Source: Aschbacher--Smith 10.1.1(7), 10.2.12, pp.741,754.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
namespace Representation.SuzukiNatural
open BenderSuzuki.MatrixGroups
noncomputable section

theorem natural_injective (m : ℕ) : Function.Injective (natural m) := by
  intro x y h
  apply (SuzukiMatrixSubgroup m).subtype_injective
  apply generalLinearNatural_injective 4
  apply LinearMap.ext
  intro v
  exact LinearMap.congr_fun h v

theorem natural_normalizer_rank (m : ℕ) (hm : 0 < m) :
    primeRank 2 (linearNormalizer (natural m)) ≤ 2*m+1 := by
  exact (BinaryScalarCommutant.normalizer_rank_le (natural m)
    (fun f hf => commuting_addHom_eq_scalar m f.toAddMonoidHom hf)
    (natural_injective m)).trans (suzuki_automorphism_two_rank m hm)

end
end Representation.SuzukiNatural
