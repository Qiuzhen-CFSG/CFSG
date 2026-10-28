module
public import Theory.SpecificGroups.Triality.OddFundamentalCentralizer.RankOne.Scalars
public import Theory.SpecificGroups.Triality.OddFundamentalCentralizer.RankOne.Kernels

/-!
# Faithfulness after the elementary central quotient

Commutation with the other two arm factors forces the split Frobenius-diagonal
kernel into the SL₂ scalar center. The three equal arm scalar involutions have
nontrivial product, so the split diagonal is faithful. After elementary descent,
faithfulness again reduces both kernels to scalars. Their actions on adjacent
fixed positive root elements exclude the nontrivial scalar from the elementary
center. This argument includes characteristic three without using perfectness.

Sources: GLS3 §§2.4 and 2.6 (`refs/KGroup/GLS3/chapter2.tex`);
Aschbacher–Smith A.2.17, printed p.39 of `refs/quasithin.pdf`.
-/

@[expose] public section
noncomputable section
open Matrix
open scoped MatrixGroups
namespace Triality.Standard.OddFundamentalCentralizer.RankOne
open Parabolics

def upper {F : Type*} [Field F] (t : F) : SL(2, F) :=
  SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) (by decide) t

lemma map_upper {F K : Type*} [Field F] [Field K] (f : F →+* K) (t : F) :
    SpecialLinearGroup.map f (upper t) = upper (f t) := by
  apply Subtype.ext
  change Matrix.map (1 + Matrix.single 0 1 t) f = 1 + Matrix.single 0 1 (f t)
  ext a b
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply, map_add]
  split_ifs <;> simp only [map_one, map_zero]

lemma map_neg_one {F K : Type*} [Field F] [Field K] (f : F →+* K) :
    SpecialLinearGroup.map f (-1 : SL(2, F)) = -1 := by
  ext i j
  change f (-((1 : Matrix (Fin 2) (Fin 2) F) i j)) =
    -((1 : Matrix (Fin 2) (Fin 2) K) i j)
  simp only [map_neg, Matrix.one_apply]
  split_ifs <;> simp only [map_one, map_zero]

lemma armsFixedEmbedding_injective (P : Parameters) :
    Function.Injective ((pinnedRankOneMaps P).armsFixedEmbedding (armRootCommutation P)) :=
  armsFixedEmbedding_injective_of_scalars _ _
    (pinned_scalar_arms P 0 2 (by decide) (by decide))
    (pinned_scalar_arms P 0 3 (by decide) (by decide))

lemma armsFixedEmbedding_neg_one (P : Parameters) :
    (pinnedRankOneMaps P).armsFixedEmbedding (armRootCommutation P) (-1) =
      (pinnedRankOneMaps P).hom 0 (-1) := by
  change (pinnedRankOneMaps P).hom 0 (-1) *
    (pinnedRankOneMaps P).hom 2 (sl2Frobenius P (-1)) *
    (pinnedRankOneMaps P).hom 3 (sl2Frobenius P (sl2Frobenius P (-1))) = _
  simp only [sl2Frobenius_neg_one]
  have hs : (pinnedRankOneMaps P).hom 0 (-1) *
      (pinnedRankOneMaps P).hom 0 (-1) = 1 := by
    simpa only [neg_mul_neg, one_mul, map_one] using
      (map_mul ((pinnedRankOneMaps P).hom 0) (-1) (-1)).symm
  calc
    _ = (pinnedRankOneMaps P).hom 0 (-1) * (pinnedRankOneMaps P).hom 0 (-1) *
        (pinnedRankOneMaps P).hom 0 (-1) :=
      congrArg₂ (· * ·) (congrArg₂ (· * ·) rfl
        (pinned_scalar_arms P 0 2 (by decide) (by decide)).symm)
        (pinned_scalar_arms P 0 3 (by decide) (by decide)).symm
    _ = _ := by rw [hs, one_mul]

lemma centralFixedEmbedding_neg_one (P : Parameters) :
    (pinnedRankOneMaps P).centralFixedEmbedding (-1) =
      (pinnedRankOneMaps P).hom 1 (-1) := by
  change (pinnedRankOneMaps P).hom 1 (SpecialLinearGroup.map _ (-1)) = _
  rw [map_neg_one]

lemma centralFixedEmbedding_upper_one (P : Parameters) :
    (pinnedRankOneMaps P).centralFixedEmbedding (upper 1) = positiveRoot P 1 1 := by
  change (pinnedRankOneMaps P).hom 1 (SpecialLinearGroup.map _ (upper 1)) = _
  rw [map_upper, map_one]
  exact (pinnedRankOneMaps P).positive 1 1

lemma armsFixedEmbedding_upper (P : Parameters) (t : ExtensionField P) :
    (pinnedRankOneMaps P).armsFixedEmbedding (armRootCommutation P) (upper t) =
      positiveRoot P 0 t * positiveRoot P 2 (fieldFrobenius P t) *
        positiveRoot P 3 (fieldFrobenius P (fieldFrobenius P t)) := by
  change (pinnedRankOneMaps P).hom 0 (upper t) *
    (pinnedRankOneMaps P).hom 2 (SpecialLinearGroup.map _ (upper t)) *
    (pinnedRankOneMaps P).hom 3
      (SpecialLinearGroup.map _ (SpecialLinearGroup.map _ (upper t))) = _
  simp only [map_upper]
  simp only [upper, (pinnedRankOneMaps P).positive]
  rfl

lemma central_scalar_arms_upper_swap (P : Parameters) (t : ExtensionField P) :
    (pinnedRankOneMaps P).hom 1 (-1) *
        (pinnedRankOneMaps P).armsFixedEmbedding (armRootCommutation P) (upper t) =
      (pinnedRankOneMaps P).armsFixedEmbedding (armRootCommutation P) (upper (-t)) *
        (pinnedRankOneMaps P).hom 1 (-1) := by
  simp only [armsFixedEmbedding_upper, map_neg]
  exact (SemiconjBy.mul_right
    (SemiconjBy.mul_right (pinned_scalar_positive_swap P 1 0 (by decide) t)
      (pinned_scalar_positive_swap P 1 2 (by decide) (fieldFrobenius P t)))
    (pinned_scalar_positive_swap P 1 3 (by decide)
      (fieldFrobenius P (fieldFrobenius P t)))).eq

lemma two_ne_zero (P : Parameters) (hp : Odd P.prime) : (2 : ExtensionField P) ≠ 0 := by
  intro h
  have hdiv : P.prime ∣ 2 := (CharP.cast_eq_zero_iff (ExtensionField P) P.prime 2).mp h
  have heq : P.prime = 2 := ((Nat.dvd_prime (by decide : Nat.Prime 2)).mp hdiv).resolve_left
    P.prime_prime.ne_one
  rw [heq] at hp
  exact (by decide : ¬Odd (2 : ℕ)) hp

lemma upper_one_ne_upper_neg_one (P : Parameters) (hp : Odd P.prime) :
    upper (1 : ExtensionField P) ≠ upper (-1) := by
  intro h
  have he := congrArg (fun A : SL(2, ExtensionField P) => A 0 1) h
  have hneg : (1 : ExtensionField P) = -1 := by
    simpa [upper, SpecialLinearGroup.transvection, Matrix.transvection,
      Matrix.one_apply, Matrix.single_apply] using he
  exact two_ne_zero P hp (by linear_combination hneg)

lemma fundamental_scalar_not_central (P : Parameters) (hp : Odd P.prime) :
    elementaryLift P (pinnedRankOneMaps P).centralFixedEmbedding
      (centralFixed_mem (pinnedRankOneMaps P)) (-1) ∉
        Subgroup.center (ElementaryGroup P) := by
  intro hz
  have h := congrArg (elementaryInclusion P) ((Subgroup.mem_center_iff.mp hz)
    (elementaryLift P ((pinnedRankOneMaps P).armsFixedEmbedding (armRootCommutation P))
      (armsFixed_mem (pinnedRankOneMaps P) (armRootCommutation P)) (upper 1)))
  simp only [map_mul, elementaryInclusion_lift, centralFixedEmbedding_neg_one] at h
  rw [central_scalar_arms_upper_swap] at h
  have hu := armsFixedEmbedding_injective P (mul_right_cancel h)
  exact upper_one_ne_upper_neg_one P hp hu

lemma arms_scalar_not_central (P : Parameters) (hp : Odd P.prime) :
    elementaryLift P ((pinnedRankOneMaps P).armsFixedEmbedding (armRootCommutation P))
      (armsFixed_mem (pinnedRankOneMaps P) (armRootCommutation P)) (-1) ∉
        Subgroup.center (ElementaryGroup P) := by
  intro hz
  have h := congrArg (elementaryInclusion P) ((Subgroup.mem_center_iff.mp hz)
    (elementaryLift P (pinnedRankOneMaps P).centralFixedEmbedding
      (centralFixed_mem (pinnedRankOneMaps P)) (upper 1)))
  simp only [map_mul, elementaryInclusion_lift, armsFixedEmbedding_neg_one,
    centralFixedEmbedding_upper_one] at h
  rw [pinned_scalar_positive_swap P 0 1 (by decide)] at h
  have he : upper (1 : ExtensionField P) = upper (-1) :=
    (pinnedRankOneMaps P).injective 1 (by
    simpa only [upper, (pinnedRankOneMaps P).positive] using mul_right_cancel h)
  exact upper_one_ne_upper_neg_one P hp he

/-- The central-root SL₂ remains faithful through the actual elementary-center quotient. -/
theorem fundamentalHom_injective (P : Parameters) (hp : Odd P.prime) :
    Function.Injective (fundamentalHom (pinnedRankOneMaps P)) :=
  descendedHom_injective_of_scalar P _ _
    (pinnedRankOneMaps P).centralFixedEmbedding_injective
    (fundamental_scalar_not_central P hp)

/-- The cubic Frobenius diagonal remains faithful through the same central quotient. -/
theorem armsHom_injective (P : Parameters) (hp : Odd P.prime) :
    Function.Injective (armsHom (pinnedRankOneMaps P) (armRootCommutation P)) :=
  descendedHom_injective_of_scalar P _ _ (armsFixedEmbedding_injective P)
    (arms_scalar_not_central P hp)

end Triality.Standard.OddFundamentalCentralizer.RankOne
