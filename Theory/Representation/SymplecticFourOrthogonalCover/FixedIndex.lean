module

public import Theory.Representation.SymplecticFourOrthogonalCover.FixedLifting
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Fixed quotient indices for every binary symplectic central cover

Every natural fixed vector has all its lifts fixed in the universal odd
orthogonal cover and every central factor. The original cover projection
therefore induces an isomorphism of fixed-space quotients for every actor
subgroup. In particular its fixed codimension agrees with the natural one,
without splitting off the fixed attachment or assuming an elementary actor.

Source: MS93 (1.5)(ii), used in the maximal-small-mover family of (5.0).
-/

public section
open Representation Representation.OneCohomology
namespace Representation.SymplecticFourOrthogonalCover
variable {K : Type*} [Field K] [Finite K] [CharP K 2] [Algebra (ZMod 2) K]
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
variable {σ : Representation (ZMod 2) (L (K := K)) W}
noncomputable def binaryCoverFixedQuotientEquiv
    (p : σ.IntertwiningMap (binaryNatural (K := K))) (hp : IsCover p)
    (A : Subgroup (L (K := K))) :
    (W ⧸ BinaryOffender.fixedSpace σ A) ≃ₗ[ZMod 2]
      Natural (K := K) ⧸ BinaryOffender.fixedSpace (binaryNatural (K := K)) A := by
  let f := (BinaryOffender.fixedSpace (binaryNatural (K := K)) A).mkQ.comp p.toLinearMap
  have hf : Function.Surjective f :=
    (Submodule.mkQ_surjective _).comp hp.1
  have hk : f.ker = BinaryOffender.fixedSpace σ A := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
    exact (cover_fixed_preimage p hp A).symm
  exact (Submodule.quotEquivOfEq _ _ hk.symm).trans (f.quotKerEquivOfSurjective hf)

theorem fixedCodim_of_binaryCover
    (p : σ.IntertwiningMap (binaryNatural (K := K))) (hp : IsCover p)
    (A : Subgroup (L (K := K))) :
    BinaryOffender.fixedCodim σ A = BinaryOffender.fixedCodim (binaryNatural (K := K)) A :=
  (binaryCoverFixedQuotientEquiv p hp A).finrank_eq
end Representation.SymplecticFourOrthogonalCover
