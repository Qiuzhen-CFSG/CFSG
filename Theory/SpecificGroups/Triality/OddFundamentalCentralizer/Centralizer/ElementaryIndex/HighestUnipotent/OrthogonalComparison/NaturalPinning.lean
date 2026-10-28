module
public import Theory.SpecificGroups.Triality.OddFundamentalCentralizer.Centralizer.ElementaryIndex.HighestUnipotent.OrthogonalComparison.Natural
public import Theory.SpecificGroups.Triality.OddFundamentalCentralizer.Centralizer.ElementaryIndex.HighestUnipotent.OrthogonalComparison.NaturalPinning.Maps
/-!
# The natural D₄ pinning with exact projective markings

The determinant-space rank-one maps have the eight prescribed natural
transvection matrices. The three arm ranges agree with the literal model
factors after the surjective inverse-transpose and sign reparametrizations.
The native Weyl word n₁(n₀n₂n₃) intertwines the central map with the first
left determinant factor, proving equality of the highest homomorphisms.
This constructs the natural-space input of the Geck comparison over every
field, in particular for all odd triality parameters.

Sources: GLS3 §§2.4, 2.6–2.7; Aschbacher–Smith A.2.17, printed pp.38–39.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
@[expose] public section
open Matrix
open scoped MatrixGroups
open ClassicalOrthogonal ClassicalOrthogonal.Fundamental ClassicalOrthogonal.Fundamental.SplitOddBlocks
namespace Triality.Standard.OddFundamentalCentralizer.ElementaryIndex.HighestUnipotent.OrthogonalComparison.PinningConstruction
noncomputable section
variable {F : Type*} [Field F]

def hom : Fin 4 → SL(2,F) →* OmegaPlus 4 F := ![arm0, central, arm2, arm3]

private lemma curve_apply (i : Fin 4) (d : Bool) (t : F) (v : VectorD 4 F) :
    naturalCurve F i d t *ᵥ v = v + t •
      (v (positions i d).1.2 • Pi.single (positions i d).1.1 (1 : F) -
        v (positions i d).2.2 • Pi.single (positions i d).2.1 (1 : F)) := by
  have hs (a b : NaturalIndex) : castMatrix F (single a b (1 : ℤ)) = single a b 1 := by
    change (single a b (1 : ℤ)).map (Int.castRingHom F) = _
    rw [Matrix.map_single, map_one]
  simp only [naturalCurve, naturalGenerator, map_sub, hs, Matrix.add_mulVec,
    Matrix.one_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.single_mulVec_eq,
    one_mul]

theorem positive (i : Fin 4) (t : F) : naturalMatrix F (hom i
    (SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) (by decide) t)) =
      naturalCurve F i true t := by
  apply Matrix.mulVec_injective
  funext v
  rw [naturalMatrix_mulVec, curve_apply]
  fin_cases i <;> funext k <;> rcases k with k | k <;> fin_cases k <;>
    simp [hom, arm0_apply, central_apply, arm2_apply, arm3_apply, positions,
      SpecialLinearGroup.transvection_coe, Matrix.one_apply, Matrix.single_apply,
      Pi.single_apply, sub_eq_add_neg] <;> ring

theorem negative (i : Fin 4) (t : F) : naturalMatrix F (hom i
    (SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) (by decide) t)) =
      naturalCurve F i false t := by
  apply Matrix.mulVec_injective
  funext v
  rw [naturalMatrix_mulVec, curve_apply]
  fin_cases i <;> funext k <;> rcases k with k | k <;> fin_cases k <;>
    simp [hom, arm0_apply, central_apply, arm2_apply, arm3_apply, positions,
      SpecialLinearGroup.transvection_coe, Matrix.one_apply, Matrix.single_apply,
      Pi.single_apply, sub_eq_add_neg] <;> ring

theorem arm0_projective :
    (projectiveElementaryMap (formD 4 F)).comp arm0 =
      OrthogonalModel.armZero.comp dual.toMonoidHom := by
  ext a
  change projectiveElementaryMap _ (rightCover _ _ _ (dual a, 1)) =
    projectiveElementaryMap _ (rightCover _ _ _ (dual a, fourMap (1, 1)))
  rw [show (1, 1) = (1 : FourPlusMatrix.PairSL (F := F)) from rfl, map_one]

theorem arm2_projective :
    (projectiveElementaryMap (formD 4 F)).comp arm2 =
      OrthogonalModel.armTwo.comp dual.toMonoidHom := by
  rfl

theorem arm3_projective :
    (projectiveElementaryMap (formD 4 F)).comp arm3 =
      OrthogonalModel.armThree.comp sign.toMonoidHom := by
  rfl

private lemma omega_mul_apply (g h : OmegaPlus 4 F) (v : VectorD 4 F) :
    (g * h).val.val v = g.val.val (h.val.val v) := rfl

private lemma weyl_val : (weylMatrix F).val = !![0, 1; -1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weylMatrix, SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply, Matrix.one_apply]

private lemma highestWeyl_apply (v : VectorD 4 F) :
    (naturalHighestWeyl F hom).val.val v = Sum.elim
      ![v (.inl 1), -v (.inr 2), v (.inl 0), -v (.inr 3)]
      ![v (.inr 1), -v (.inl 2), v (.inr 0), -v (.inl 3)] := by
  simp only [naturalHighestWeyl, omega_mul_apply]
  funext k
  rcases k with k | k <;> fin_cases k <;>
    simp [hom, central_apply, arm0_apply, arm2_apply, arm3_apply, weyl_val]

private lemma highestCover_apply (a : SL(2,F)) (v : VectorD 4 F) :
    (leftCover (formD 2 F) (formD 4 F) (splitDIsometry 2 2).symm a).val.val v = Sum.elim
      ![a 0 0 * v (.inl 0) - a 0 1 * v (.inr 1),
        a 0 0 * v (.inl 1) + a 0 1 * v (.inr 0), v (.inl 2), v (.inl 3)]
      ![a 1 0 * v (.inl 1) + a 1 1 * v (.inr 0),
        -(a 1 0 * v (.inl 0)) + a 1 1 * v (.inr 1), v (.inr 2), v (.inr 3)] := by
  change (splitD (F := F) 2 2).symm
    (FourPlusMatrix.coordinates.symm (a.val *
      FourPlusMatrix.coordinates ((splitD 2 2 v).1) * (1 : SL(2,F))⁻¹.val),
      (1 : OmegaPlus 2 F).val.val ((splitD 2 2 v).2)) = _
  funext k
  rcases k with k | k <;> fin_cases k <;>
    simp [splitD, FourPlusMatrix.coordinates, Matrix.mul_apply, Fin.sum_univ_two,
      Fin.addCases] <;> ring

private lemma highest_intertwines (a : SL(2,F)) :
    naturalHighestWeyl F hom * hom 1 a =
      leftCover (formD 2 F) (formD 4 F) (splitDIsometry 2 2).symm a *
        naturalHighestWeyl F hom := by
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  simp only [omega_mul_apply, highestWeyl_apply, highestCover_apply]
  funext k
  rcases k with k | k <;> fin_cases k <;>
    simp [hom, central_apply] <;> ring


theorem highest_eq : naturalHighestHom F hom = OrthogonalModel.highest := by
  ext a
  change projectiveElementaryMap _
    (naturalHighestWeyl F hom * hom 1 a * (naturalHighestWeyl F hom)⁻¹) =
      projectiveElementaryMap _ (leftCover (formD 2 F) (formD 4 F)
        (splitDIsometry 2 2).symm a)
  rw [highest_intertwines, mul_assoc, mul_inv_cancel, mul_one]

theorem armZero_range : ((projectiveElementaryMap (formD 4 F)).comp (hom 0)).range =
    OrthogonalModel.armZero.range := by
  change ((projectiveElementaryMap (formD 4 F)).comp arm0).range = _
  have hd : (dual (F := F)).toMonoidHom.range = ⊤ :=
    MonoidHom.range_eq_top.mpr (dual (F := F)).surjective
  rw [arm0_projective, MonoidHom.range_comp, hd, ← MonoidHom.range_eq_map]

theorem armTwo_range : ((projectiveElementaryMap (formD 4 F)).comp (hom 2)).range =
    OrthogonalModel.armTwo.range := by
  change ((projectiveElementaryMap (formD 4 F)).comp arm2).range = _
  have hd : (dual (F := F)).toMonoidHom.range = ⊤ :=
    MonoidHom.range_eq_top.mpr (dual (F := F)).surjective
  rw [arm2_projective, MonoidHom.range_comp, hd, ← MonoidHom.range_eq_map]

theorem armThree_range : ((projectiveElementaryMap (formD 4 F)).comp (hom 3)).range =
    OrthogonalModel.armThree.range := by
  change ((projectiveElementaryMap (formD 4 F)).comp arm3).range = _
  have hs : (sign (F := F)).toMonoidHom.range = ⊤ :=
    MonoidHom.range_eq_top.mpr (sign (F := F)).surjective
  rw [arm3_projective, MonoidHom.range_comp, hs, ← MonoidHom.range_eq_map]

end
end Triality.Standard.OddFundamentalCentralizer.ElementaryIndex.HighestUnipotent.OrthogonalComparison.PinningConstruction

namespace Triality.Standard.OddFundamentalCentralizer.ElementaryIndex.HighestUnipotent.OrthogonalComparison
noncomputable section

/-- The prescribed D₄ pinning in the actual elementary orthogonal eight-space. -/
def naturalPinning (F : Type*) [Field F] : NaturalPinning F where
  hom := PinningConstruction.hom
  positive := PinningConstruction.positive
  negative := PinningConstruction.negative
  highest_range := congrArg MonoidHom.range PinningConstruction.highest_eq
  armZero_range := PinningConstruction.armZero_range
  armTwo_range := PinningConstruction.armTwo_range
  armThree_range := PinningConstruction.armThree_range

/-- In particular the natural pinning exists for every odd triality parameter,
including characteristic three and exponent one. -/
theorem nonempty_naturalPinning (P : Parameters) (_hp : Odd P.prime) :
    Nonempty (NaturalPinning (ExtensionField P)) := ⟨naturalPinning _⟩

end
end Triality.Standard.OddFundamentalCentralizer.ElementaryIndex.HighestUnipotent.OrthogonalComparison
