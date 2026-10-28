module
public import Theory.Representation.BinaryScalarCommutant
public import Theory.Representation.OrthogonalFourMinusRankOne.AmbientActions.ScalarCentralizer
public import Theory.SpecificGroups.PSL2.BinaryAutomorphismRank

/-!
# The full binary normalizer of the minus-type orthogonal four-space

The literal Hermitian action of SL₂(2^(2s)) is faithful and its additive
commutant consists of scalars over GF(2^s). A scalar involution is identity,
so the full normalizer has two-rank at most 2s by the automorphism bound.
Source: Aschbacher--Smith 10.1.1(4), 10.2.12, pp.741,754.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
namespace Representation.OrthogonalFourMinus.RankOne
open FiniteModel
noncomputable section
variable (s : ℕ) [NeZero s]
local instance normalizerBinaryAlgebra : Algebra (ZMod 2) (fixedField s) := ZMod.algebra _ 2
local instance normalizerBinaryModule : Module (ZMod 2) (Space s) :=
  Module.compHom (Space s) (algebraMap (ZMod 2) (fixedField s))

theorem hermitian_injective : Function.Injective (SL2.BinarySmall.hermitian s) := by
  intro x y h
  apply action_injective s
  apply LinearMap.ext
  intro v
  exact LinearMap.congr_fun h v

theorem hermitian_normalizer_rank :
    primeRank 2 (linearNormalizer (SL2.BinarySmall.hermitian s)) ≤ 2*s := by
  let : Nontrivial (Space s) := (coordinates s).toEquiv.nontrivial
  apply (BinaryScalarCommutant.normalizer_rank_le (SL2.BinarySmall.hermitian s)
    (AmbientActions.commuting_binaryEnd_eq_scalar s) (hermitian_injective s)).trans
  exact Theory.PSL2.BinaryAutomorphismRank.sl2_automorphism_two_rank_le
    (by have := NeZero.pos s; omega)
    (GaloisField.card 2 (2*s) (by have := NeZero.ne s; omega))

end
end Representation.OrthogonalFourMinus.RankOne
