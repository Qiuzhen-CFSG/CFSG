module
public import Theory.SpecificGroups.Triality.OddFundamentalCentralizer.Centralizer.Lifts
public import Theory.SpecificGroups.Triality.OddFundamentalCentralizer.Centralizer.Geometry.Specialization

/-!
# The complementary rank-one geometry in odd triality

For the literal pinned maps, the inverse conjugate of the three-arm Frobenius
diagonal commutes with the central SL₂, and the two maps have the same image
of −1. The proof specializes checked integral D4 matrices and uses generation
by the two root curves. It includes characteristic three and does not require
perfectness. The calculation in fact works in every characteristic.

The final applications discharge the commutation and shared-scalar inputs of
`Descent`; faithfulness after the central quotient remains explicit. This is
the complementary-factor part of Aschbacher–Smith A.2.17, printed p.39, (*) and
the final triality paragraph, using GLS3 §§2.4 and 2.6. Centralizer exhaustion
is a separate result.
-/
@[expose] public section
noncomputable section
open Matrix
open scoped MatrixGroups
namespace Triality.Standard.OddFundamentalCentralizer
open Parabolics

namespace Geometry

variable {P : Parameters} (D : PinnedRankOneMaps P) (C : ArmRootCommutation P)

private def signedRoot (i : Fin 4) (b : Bool) (t : ExtensionField P) : SplitGroup P :=
  if b then positiveRoot P i t else negativeRoot P i t

private lemma matrixHom_signedRoot (i : Fin 4) (b : Bool) (t : ExtensionField P) :
    matrixHom P (signedRoot i b t) = curve i b t := by
  cases b
  · exact matrixHom_negative P i t
  · exact matrixHom_positive P i t

private lemma matrixHom_conjugatedRoot (b : Bool) (t : ExtensionField P) :
    matrixHom P ((MulAut.conj (splitHighestWeyl D C)) (signedRoot 1 b t)) =
      highestCurve b t := by
  change matrixHom P (splitHighestWeyl D C * signedRoot 1 b t *
    (splitHighestWeyl D C)⁻¹) = _
  simp only [map_mul, matrixHom_signedRoot, matrixHom_highest]
  rw [highest_curve, mul_assoc, ← matrixHom_highest D C, ← map_mul,
    mul_inv_cancel, map_one, mul_one]

/-- Conjugation sends the central root curves to curves commuting with every arm. -/
theorem conjugatedRoot_commute (i : Fin 4) (hi : i ≠ 1)
    (b c : Bool) (t u : ExtensionField P) :
    Commute ((MulAut.conj (splitHighestWeyl D C))
      (if b then positiveRoot P 1 t else negativeRoot P 1 t))
      (if c then positiveRoot P i u else negativeRoot P i u) := by
  change Commute ((MulAut.conj (splitHighestWeyl D C)) (signedRoot 1 b t))
    (signedRoot i c u)
  apply matrixHom_injective P
  simpa only [map_mul, matrixHom_conjugatedRoot, matrixHom_signedRoot] using
    (highest_curve_commute i hi b c t u).eq

/-- Root generation extends the integral calculation to both full split factors. -/
theorem conjugatedCentral_commute_arm (i : Fin 4) (hi : i ≠ 1)
    (a b : SL(2, ExtensionField P)) :
    Commute ((MulAut.conj (splitHighestWeyl D C)) (D.hom 1 a)) (D.hom i b) := by
  have hr (s : Bool) (t : ExtensionField P) (g : SL(2, ExtensionField P)) :
      Commute ((MulAut.conj (splitHighestWeyl D C))
        (if s then positiveRoot P 1 t else negativeRoot P 1 t)) (D.hom i g) := by
    apply sl2_root_induction (fun g => Commute ((MulAut.conj (splitHighestWeyl D C))
      (if s then positiveRoot P 1 t else negativeRoot P 1 t)) (D.hom i g)) ?_ ?_ ?_ g
    · intro u
      exact (congrArg (fun x : SplitGroup P => Commute
        ((MulAut.conj (splitHighestWeyl D C))
          (if s then positiveRoot P 1 t else negativeRoot P 1 t)) x)
        (D.positive i u)).mpr (conjugatedRoot_commute D C i hi s true t u)
    · intro u
      exact (congrArg (fun x : SplitGroup P => Commute
        ((MulAut.conj (splitHighestWeyl D C))
          (if s then positiveRoot P 1 t else negativeRoot P 1 t)) x)
        (D.negative i u)).mpr (conjugatedRoot_commute D C i hi s false t u)
    · intro x y hx hy
      simpa only [map_mul] using hx.mul_right hy
  apply sl2_root_induction (fun a => Commute
    ((MulAut.conj (splitHighestWeyl D C)) (D.hom 1 a)) (D.hom i b)) ?_ ?_ ?_ a
  · intro t
    exact (congrArg (fun x : SplitGroup P => Commute
      ((MulAut.conj (splitHighestWeyl D C)) x) (D.hom i b))
      (D.positive 1 t)).mpr (hr true t b)
  · intro t
    exact (congrArg (fun x : SplitGroup P => Commute
      ((MulAut.conj (splitHighestWeyl D C)) x) (D.hom i b))
      (D.negative 1 t)).mpr (hr false t b)
  · intro x y hx hy
    simpa only [map_mul] using hx.mul_left hy

lemma map_neg_one {K L : Type*} [Field K] [Field L] (f : K →+* L) :
    SpecialLinearGroup.map f (-1 : SL(2, K)) = -1 := by
  apply Subtype.ext
  change f.mapMatrix (-1) = -1
  simp only [map_neg, map_one]

lemma pinned_scalar_arm (i : Fin 4) (hi : i ≠ 1) : D.hom i (-1) = D.hom 0 (-1) := by
  apply matrixHom_injective P
  rw [matrixHom_scalar, matrixHom_scalar, Integral.scalar_arms i hi]

lemma arms_scalar : D.armsFixedEmbedding C (-1) = D.hom 0 (-1) := by
  have hf : sl2Frobenius P (-1) = -1 := map_neg_one _
  change D.hom 0 (-1) * D.hom 2 (sl2Frobenius P (-1)) *
    D.hom 3 (sl2Frobenius P (sl2Frobenius P (-1))) = _
  simp only [hf, pinned_scalar_arm D 2 (by decide), pinned_scalar_arm D 3 (by decide)]
  rw [← map_mul, ← map_mul]
  simp

lemma weyl_scalar : splitHighestWeyl D C * D.hom 1 (-1) =
    D.hom 0 (-1) * splitHighestWeyl D C := by
  apply matrixHom_injective P
  simp only [map_mul, matrixHom_highest, matrixHom_scalar]
  simpa only [map_mul] using congrArg (specialize (F := ExtensionField P)) Integral.highest_scalar

end Geometry

variable {P : Parameters} (D : PinnedRankOneMaps P) (C : ArmRootCommutation P)

/-- The exact split commutation required by the elementary and quotient lifts.
The inverse conjugation agrees with `splitComplementHom`. -/
theorem centralFixedEmbedding_splitComplementHom_commute
    (a : SL(2, GaloisField P.prime P.exponent)) (b : SL(2, ExtensionField P)) :
    Commute (D.centralFixedEmbedding a) (splitComplementHom D C b) := by
  have h : Commute ((MulAut.conj (splitHighestWeyl D C)) (D.centralFixedEmbedding a))
      (D.armsFixedEmbedding C b) :=
    ((Geometry.conjugatedCentral_commute_arm D C 0 (by decide) (sl2BaseEmbedding P a) b).mul_right
      (Geometry.conjugatedCentral_commute_arm D C 2 (by decide) (sl2BaseEmbedding P a)
        (sl2Frobenius P b))).mul_right
      (Geometry.conjugatedCentral_commute_arm D C 3 (by decide) (sl2BaseEmbedding P a)
        (sl2Frobenius P (sl2Frobenius P b)))
  have hm := h.map (MulAut.conj (splitHighestWeyl D C)⁻¹).toMonoidHom
  simpa [splitComplementHom, MulAut.conj_apply, mul_assoc] using hm

/-- The scalar in the two literal split SL₂ maps is the same. -/
theorem centralFixedEmbedding_neg_one_eq_splitComplementHom :
    D.centralFixedEmbedding (-1) = splitComplementHom D C (-1) := by
  have hb : sl2BaseEmbedding P (-1) = -1 := Geometry.map_neg_one _
  have hc : D.centralFixedEmbedding (-1) = D.hom 1 (-1) := congrArg (D.hom 1) hb
  have hw := congrArg (fun x : SplitGroup P => (splitHighestWeyl D C)⁻¹ * x)
    (Geometry.weyl_scalar D C)
  have hs : D.hom 1 (-1) = (splitHighestWeyl D C)⁻¹ * D.hom 0 (-1) * splitHighestWeyl D C := by
    simpa only [← mul_assoc, inv_mul_cancel, one_mul] using hw
  have ha := congrArg (MulAut.conj (splitHighestWeyl D C)⁻¹) (Geometry.arms_scalar D C)
  have ha' : splitComplementHom D C (-1) =
      (splitHighestWeyl D C)⁻¹ * D.hom 0 (-1) * splitHighestWeyl D C := by
    change (MulAut.conj (splitHighestWeyl D C)⁻¹) (D.armsFixedEmbedding C (-1)) = _
    simpa only [MulAut.conj_apply, inv_inv] using ha
  exact hc.trans (hs.trans ha'.symm)

/-- The integral calculation discharges the exact commutation premise of Descent. -/
theorem fundamentalHom_complementHom_commute
    (a : SL(2, GaloisField P.prime P.exponent)) (b : SL(2, ExtensionField P)) :
    Commute (fundamentalHom D a) (complementHom D C b) :=
  fundamentalHom_complementHom_commute_of_split D C
    (centralFixedEmbedding_splitComplementHom_commute D C) a b

/-- The shared scalar survives the actual elementary restriction and central quotient. -/
theorem fundamentalHom_neg_one_eq_complementHom :
    fundamentalHom D (-1) = complementHom D C (-1) :=
  fundamentalHom_neg_one_eq_complementHom_of_split D C
    (centralFixedEmbedding_neg_one_eq_splitComplementHom D C)

/-- The source's common-scalar intersection, retaining only quotient faithfulness. -/
theorem mem_fundamental_inf_complement_iff
    (hk : Function.Injective (fundamentalHom D)) (x : Carrier P) :
    x ∈ fundamental P ⊓ (complementHom D C).range ↔
      x = 1 ∨ x = fundamentalHom D (-1) :=
  mem_fundamental_inf_range_iff D (complementHom D C)
    (fundamentalHom_complementHom_commute D C) hk
    (fundamentalHom_neg_one_eq_complementHom D C) x

/-- The complementary cubic field supplies the rank lower bound in A.2.17 (*).
Only faithfulness after the central quotient remains as an independent input. -/
theorem three_mul_exponent_le_residual_rank_of_geometry
    (hj : Function.Injective (complementHom D C)) :
    3 * P.exponent ≤ primeRank P.prime (residual P) :=
  three_mul_exponent_le_residual_rank D (complementHom D C)
    (fundamentalHom_complementHom_commute D C) hj

end Triality.Standard.OddFundamentalCentralizer
