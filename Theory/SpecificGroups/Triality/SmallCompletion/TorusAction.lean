module
public import Theory.SpecificGroups.Triality.TwoLocalCover.ApartmentStabilizer.Opposition

/-!
# The native triality half-turn inverts the Cartan

The opposition word negates every D4 root. Its conjugation swaps the positive
and negative simple curves; a pinned SL2 calculation therefore inverts each
coroot word. Multiplicative torus coordinates extend this to the whole split
Cartan, and faithful descent gives inversion on the actual triality carrier.
This calculation holds for every positive binary exponent.

Source: GLS3 §§2.3--2.4 (`refs/KGroup/GLS3/chapter2.tex`) and the marked
Cartan calculation in Aschbacher--Smith F.4.10,16, pp.279,282.
-/

@[expose] public noncomputable section
open Matrix
open scoped MatrixGroups
open Theory.AlgebraicGroup.StandardRootSystem RootPairing.IntegralGeckConstruction
namespace Triality.Standard.SmallCompletion
open Parabolics ConcreteBruhat Parabolics.RankOneMatrices
local instance : InvolutiveNeg (TypeDRootIndex (2+2)) := (typeDRootPairing 2).indexNeg

private theorem opposition_positive (m : ℕ) (hm : 0 < m) (i : Fin 4)
    (t : ExtensionField (binaryParameters m hm)) :
    (MulAut.conj (splitRepresentative (binaryParameters m hm) (binaryParameters_prime m hm) (.r 3)))
      (positiveRoot _ i t) = negativeRoot _ i t := by
  apply Subtype.ext
  change (splitRepresentative (binaryParameters m hm) (binaryParameters_prime m hm) (.r 3)).val * _ *
    (splitRepresentative (binaryParameters m hm) (binaryParameters_prime m hm) (.r 3)).val⁻¹ = _
  have h := splitRepresentative_rootCurveUnit_conjugation (binaryParameters m hm) (binaryParameters_prime m hm)
    (.r 3) (typeDSimpleRootIndex 2 i) t
  rw [TwoLocalGeometry.ApartmentStabilizer.opposition_root] at h
  simp only [←typeDRootPairing_baseEquiv_val,rootCurveUnit_simple,rootCurveUnit_neg_simple] at h
  exact h

private theorem opposition_negative (m : ℕ) (hm : 0 < m) (i : Fin 4)
    (t : ExtensionField (binaryParameters m hm)) :
    (MulAut.conj (splitRepresentative (binaryParameters m hm) (binaryParameters_prime m hm) (.r 3)))
      (negativeRoot _ i t) = positiveRoot _ i t := by
  apply Subtype.ext
  change (splitRepresentative (binaryParameters m hm) (binaryParameters_prime m hm) (.r 3)).val * _ *
    (splitRepresentative (binaryParameters m hm) (binaryParameters_prime m hm) (.r 3)).val⁻¹ = _
  have h := splitRepresentative_rootCurveUnit_conjugation (binaryParameters m hm) (binaryParameters_prime m hm)
    (.r 3) (-typeDSimpleRootIndex 2 i) t
  rw [TwoLocalGeometry.ApartmentStabilizer.opposition_root,neg_neg] at h
  simp only [←typeDRootPairing_baseEquiv_val,rootCurveUnit_simple,rootCurveUnit_neg_simple] at h
  exact h

private abbrev up {F : Type*} [Field F] (t : F) : SL(2,F) :=
  SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) (by decide) t
private abbrev lo {F : Type*} [Field F] (t : F) : SL(2,F) :=
  SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) (by decide) t

private theorem swapped_word {F : Type*} [Field F] (t : Fˣ) :
    lo t.val * up (-t.val⁻¹) * lo t.val * (lo (-1) * up 1 * lo (-1)) =
      (up t.val * lo (-t.val⁻¹) * up t.val * (up (-1) * lo 1 * up (-1)))⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [up,lo,SpecialLinearGroup.coe_mul,SpecialLinearGroup.transvection_coe,
      Matrix.mul_apply,Fin.sum_univ_two,Matrix.one_apply,Matrix.single_apply,t.ne_zero]

private theorem opposition_torusWord (m : ℕ) (hm : 0 < m) (i : Fin 4)
    (t : (ExtensionField (binaryParameters m hm))ˣ) :
    (MulAut.conj (splitRepresentative (binaryParameters m hm) (binaryParameters_prime m hm) (.r 3)))
      (torusWord _ i t) = (torusWord _ i t)⁻¹ := by
  let := rankOneExtensionCharTwo (binaryParameters m hm) (binaryParameters_prime m hm)
  simp only [torusWord,weylWord,map_mul,opposition_positive,opposition_negative]
  apply Subtype.ext
  have hh := congrArg (ambientHom (F := ExtensionField (binaryParameters m hm)) i) (swapped_word t)
  simp only [map_mul,map_inv] at hh
  simp only [up,lo,ambientHom_positive,ambientHom_negative] at hh
  simp only [Subgroup.coe_mul,Subgroup.coe_inv,positiveRoot,negativeRoot,inv_neg,inv_one,neg_neg]
  exact hh

private theorem opposition_product (m : ℕ) (hm : 0 < m)
    (a : TorusCoordinates.Coordinates (binaryParameters m hm)) :
    (MulAut.conj (splitRepresentative (binaryParameters m hm) (binaryParameters_prime m hm) (.r 3)))
      (TorusCoordinates.product (binaryParameters m hm) a) =
        (TorusCoordinates.product (binaryParameters m hm) a)⁻¹ := by
  have he : (MulAut.conj (splitRepresentative (binaryParameters m hm) (binaryParameters_prime m hm) (.r 3))) (TorusCoordinates.product (binaryParameters m hm) a) =
      TorusCoordinates.product (binaryParameters m hm) a⁻¹ := by
    simp only [TorusCoordinates.product,map_mul,opposition_torusWord]
    have hi (i : Fin 4) : torusWord (binaryParameters m hm) i ((a⁻¹) i) = (torusWord (binaryParameters m hm) i (a i))⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [←TorusCoordinates.torusWord_mul (binaryParameters m hm) (binaryParameters_prime m hm),Pi.inv_apply,inv_mul_cancel,TorusCoordinates.torusWord_one (binaryParameters m hm) (binaryParameters_prime m hm)]
    simp only [hi]
  exact he.trans (map_inv (TorusCoordinates.productHom (binaryParameters m hm) (binaryParameters_prime m hm)) a)

private theorem inverts_torus_of_inverts_products (P : Parameters) (hp : P.prime=2)
    (w : SplitGroup P)
    (h : ∀ a : TorusCoordinates.Coordinates P,
      (MulAut.conj w) (TorusCoordinates.product P a)=(TorusCoordinates.product P a)⁻¹)
    (t : SplitGroup P) (ht : t ∈ splitTorus P) : (MulAut.conj w) t=t⁻¹ := by
  have hs : t ∈ Set.range (TorusCoordinates.product P) := by
    rw [TorusCoordinates.range_product P hp]
    exact ht
  obtain ⟨a,rfl⟩ := hs
  exact h a

/-- The literal folded half-turn inverts every element of the native Cartan. -/
theorem simpleProduct_cube_inverts (m : ℕ) (hm : 0 < m)
    (t : torus (binaryParameters m hm)) :
    (simpleRepresentative (binaryParameters m hm) (binaryParameters_prime m hm) .arms *
      simpleRepresentative (binaryParameters m hm) (binaryParameters_prime m hm) .central)^3 * t.val *
      ((simpleRepresentative (binaryParameters m hm) (binaryParameters_prime m hm) .arms *
        simpleRepresentative (binaryParameters m hm) (binaryParameters_prime m hm) .central)^3)⁻¹ = t.val⁻¹ := by
  have hw : (simpleRepresentative (binaryParameters m hm) (binaryParameters_prime m hm) .arms * simpleRepresentative (binaryParameters m hm) (binaryParameters_prime m hm) .central)^3 =
      weylRepresentative (binaryParameters m hm) (binaryParameters_prime m hm) (.r 3) := by
    change _ = toCarrier (binaryParameters m hm) ((simpleElementary (binaryParameters m hm) (binaryParameters_prime m hm) .arms * simpleElementary (binaryParameters m hm) (binaryParameters_prime m hm) .central)^3)
    simp only [map_pow,map_mul,simpleRepresentative]
  rw [hw]
  apply FixedDescent.carrierToSplit_injective (binaryParameters m hm) (binaryParameters_prime m hm)
  simp only [map_mul,map_inv]
  rw [FixedDescent.carrierToSplit_representative]
  have ht : t.val ∈ descendSubgroup (binaryParameters m hm) (splitTorus (binaryParameters m hm)) := t.property
  have ht' : FixedDescent.carrierToSplit (binaryParameters m hm) (binaryParameters_prime m hm) t.val ∈
      splitTorus (binaryParameters m hm) :=
    (FixedDescent.mem_descend_iff (binaryParameters m hm) (binaryParameters_prime m hm) _ _).mp ht
  exact inverts_torus_of_inverts_products (binaryParameters m hm) (binaryParameters_prime m hm)
    _ (opposition_product m hm) _ ht'

end Triality.Standard.SmallCompletion
