module

public import Theory.Representation.SL2.BinarySmallModels
public import Theory.Representation.PGroupRegularOrbit
public import Theory.SpecificGroups.SL2.UpperUnipotent
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# A regular orbit basis for the SL₂(8) triple tensor

The upper root group acts regularly on the orbit of tensor basis vector 111.
The 000 coordinate of its orbit sum is the sum of seventh powers in the
field of eight elements. Every nonzero summand is one, so this sum is
nonzero in characteristic two. The p-group orbit-map theorem then gives
an actual basis, since both the tensor dimension and root-group order are eight.

This is an explicit instance of the Steinberg-module observation preceding
K.3.1 in Aschbacher–Smith, combined manuscript (1 March 2004), printed p.453.
It supplies the fixed-space calculation used to exclude the exceptional tensor.
-/

@[expose] public section

open scoped MatrixGroups TensorProduct BigOperators
open Module Matrix.SpecialLinearGroup
namespace Representation.SL2.BinarySmall.TripleFixedSpaces
noncomputable section
variable {K : Type*} [Field K] [Finite K] [CharP K 2]

def tensorBasis : Basis ((Fin 2 × Fin 2) × Fin 2) K (TripleSpace K) :=
  ((Pi.basisFun K (Fin 2)).tensorProduct (Pi.basisFun K (Fin 2))).tensorProduct
    (Pi.basisFun K (Fin 2))

omit [Finite K] [CharP K 2] in
lemma finrank_triple : finrank K (TripleSpace K) = 8 := by
  rw [finrank_eq_card_basis (tensorBasis (K := K))]
  decide

lemma orbit_coordinate (t : Multiplicative K) :
    (tensorBasis (K := K)).repr
      (triple (upperUnipotentHom K t) (tensorBasis ((1,1),1))) ((0,0),0) =
      t.toAdd ^ 7 := by
  simp only [tensorBasis, Basis.tensorProduct_apply, triple_apply_tmul,
    Basis.tensorProduct_repr_tmul_apply]
  simp [frobeniusNatural_apply, upperUnipotentHom, transvection_coe,
    Pi.basisFun_repr, Pi.basisFun_apply, iterateFrobenius_def, frobenius_def, smul_eq_mul]
  ring

omit [Finite K] in
lemma sum_seventh [Fintype K] (hK : Nat.card K = 8) :
    (∑ t : K, t ^ 7) ≠ 0 := by
  classical
  have hc : Fintype.card K = 8 := by rwa [← Nat.card_eq_fintype_card]
  have hpow (t : K) : t ^ 7 = if t = 0 then 0 else 1 := by
    split_ifs with ht
    · simp [ht]
    · simpa [hc] using FiniteField.pow_card_sub_one_eq_one t ht
  simp_rw [hpow]
  have hfilter : (Finset.univ.filter (fun t : K => ¬ t = 0)) = Finset.univ.erase 0 := by
    ext t
    simp
  simp only [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const,
    nsmul_eq_mul, mul_one, hfilter, Finset.card_erase_of_mem (Finset.mem_univ (0 : K)),
    Finset.card_univ, hc]
  norm_num only
  exact (CharP.cast_eq_zero_iff K 2 7).not.mpr (by decide)

lemma orbit_sum_ne_zero [Fintype K] (hK : Nat.card K = 8) :
    (∑ t : Multiplicative K,
      triple (upperUnipotentHom K t) (tensorBasis ((1,1),1))) ≠ 0 := by
  intro hz
  have hz' := congrArg (fun v => (tensorBasis (K := K)).repr v ((0,0),0)) hz
  simp only [map_sum, Finsupp.finsetSum_apply, orbit_coordinate, map_zero,
    Finsupp.zero_apply] at hz'
  apply sum_seventh hK
  exact (Fintype.sum_equiv (Multiplicative.toAdd : Multiplicative K ≃ K)
    (fun t => t.toAdd ^ 7) (fun t => t ^ 7) (fun _ => rfl)).symm.trans hz'

noncomputable def upperOrbitBasis [Fintype K] (hK : Nat.card K = 8) :
    Basis (Multiplicative K) K (TripleSpace K) :=
  PGroupRegularOrbit.orbitBasis (E := K) (P := Multiplicative K) (V := TripleSpace K)
    (by rw [ringChar.eq K 2]; decide)
    (by rw [ringChar.eq K 2]; apply IsPGroup.of_card (n := 3); simpa using hK)
    ((triple (K := K)).comp (upperUnipotentHom K))
    (tensorBasis ((1,1),1)) (orbit_sum_ne_zero hK)
    (by rw [finrank_triple]; simpa [Nat.card_eq_fintype_card] using hK.symm)

lemma upperOrbitBasis_apply [Fintype K] (hK : Nat.card K = 8) (g : Multiplicative K) :
    upperOrbitBasis hK g = triple (upperUnipotentHom K g) (tensorBasis ((1,1),1)) :=
  PGroupRegularOrbit.orbitBasis_apply _ _ _ _ _ _ g

lemma upperOrbitBasis_equivariant [Fintype K] (hK : Nat.card K = 8)
    (g i : Multiplicative K) :
    triple (upperUnipotentHom K g) (upperOrbitBasis hK i) = upperOrbitBasis hK (g * i) := by
  simp only [upperOrbitBasis_apply, map_mul, Module.End.mul_apply]

end
end Representation.SL2.BinarySmall.TripleFixedSpaces
