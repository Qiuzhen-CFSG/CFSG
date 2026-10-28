module

public import Theory.SpecificGroups.Triality.ConcreteBruhat.SplitNormalForm.Inputs

/-!
# Pinned rank-one reductions for the original split parabolics

The proved faithful SL₂ maps give the numbered simple Weyl involutions and
their interchange of positive and negative simple curves. Consequently the
original parabolic, defined by adjoining negative curves to the Borel, is
exactly the subgroup obtained by adjoining the corresponding Weyl words.
This is a generator equality, before any Bruhat or fixed-point assertion.

Source: the rank-one identities of GLS3 §2.4 and Definition 2.6.4,
`refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public section
noncomputable section
open Matrix
open scoped MatrixGroups
namespace Triality.Standard.ConcreteBruhat.SplitNormalForm
open Parabolics

private abbrev upper {F : Type*} [Field F] (t : F) : SL(2, F) :=
  SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) (by decide) t
private abbrev lower {F : Type*} [Field F] (t : F) : SL(2, F) :=
  SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) (by decide) t
private def rankOneWeyl (F : Type*) [Field F] : SL(2, F) :=
  upper 1 * lower 1 * upper 1

private theorem rankOneWeyl_sq (F : Type*) [Field F] [CharP F 2] :
    rankOneWeyl F ^ 2 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rankOneWeyl, upper, lower, pow_two, SpecialLinearGroup.coe_mul,
      SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply, Matrix.single_apply, CharTwo.add_self_eq_zero]

private theorem rankOneWeyl_upper (F : Type*) [Field F] [CharP F 2] (t : F) :
    rankOneWeyl F * upper t * rankOneWeyl F = lower t := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rankOneWeyl, upper, lower, SpecialLinearGroup.coe_mul,
      SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply, Matrix.single_apply, CharTwo.add_self_eq_zero]

private theorem pinned_weyl (P : Parameters) (hp : P.prime = 2) (i : Fin 4) :
    (pinnedRankOneMaps P hp).hom i (rankOneWeyl (ExtensionField P)) = weylWord P i 1 := by
  let := rankOneExtensionCharTwo P hp
  simp only [rankOneWeyl, map_mul, upper, lower, PinnedRankOneMaps.positive,
    PinnedRankOneMaps.negative, weylWord, inv_one, CharTwo.neg_eq]

/-- The numbered simple matrix representative is an involution. -/
theorem weylWord_sq (P : Parameters) (hp : P.prime = 2) (i : Fin 4) :
    weylWord P i 1 ^ 2 = 1 := by
  let := rankOneExtensionCharTwo P hp
  rw [← pinned_weyl P hp i, ← map_pow, rankOneWeyl_sq, map_one]

/-- The actual pinned matrix word exchanges the two simple curves. -/
theorem weylWord_positive (P : Parameters) (hp : P.prime = 2)
    (i : Fin 4) (t : ExtensionField P) :
    weylWord P i 1 * positiveRoot P i t * weylWord P i 1 = negativeRoot P i t := by
  let := rankOneExtensionCharTwo P hp
  have h := congrArg ((pinnedRankOneMaps P hp).hom i)
    (rankOneWeyl_upper (ExtensionField P) t)
  simpa only [map_mul, pinned_weyl, upper, lower,
    PinnedRankOneMaps.positive, PinnedRankOneMaps.negative] using h

private theorem positive_mem_borel (P : Parameters) (i : Fin 4) (t : ExtensionField P) :
    positiveRoot P i t ∈ splitBorel P :=
  Subgroup.mem_sup_left (Subgroup.subset_closure ⟨i, t, rfl⟩)

/-- Replace all negative-root generators by one Weyl generator at each marked node. -/
theorem splitParabolic_eq_borel_sup_weyl (P : Parameters) (hp : P.prime = 2) (a : Node) :
    splitParabolic P a = splitBorel P ⊔
      Subgroup.closure {g | ∃ i ∈ a.support, g = weylWord P i 1} := by
  apply le_antisymm
  · apply sup_le le_sup_left
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨i, hi, t, rfl⟩
    rw [← weylWord_positive P hp i t]
    have hw : weylWord P i 1 ∈ splitBorel P ⊔
        Subgroup.closure {g | ∃ i ∈ a.support, g = weylWord P i 1} :=
      Subgroup.mem_sup_right (Subgroup.subset_closure ⟨i, hi, rfl⟩)
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hw
      (Subgroup.mem_sup_left (positive_mem_borel P i t))) hw
  · apply sup_le le_sup_left
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨i, hi, rfl⟩
    have hpos : positiveRoot P i 1 ∈ splitParabolic P a :=
      Subgroup.mem_sup_left (positive_mem_borel P i 1)
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hpos
      (Subgroup.mem_sup_right (Subgroup.subset_closure ⟨i, hi, _, rfl⟩))) hpos

/-- The Borel and the actual split Weyl subgroup generate every split matrix. -/
theorem borel_sup_weyl_eq_top (P : Parameters) (hp : P.prime = 2) :
    splitBorel P ⊔ splitWeylSubgroup P = ⊤ := by
  have h (a : Node) : splitParabolic P a ≤ splitBorel P ⊔ splitWeylSubgroup P := by
    rw [splitParabolic_eq_borel_sup_weyl P hp a]
    apply sup_le le_sup_left
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨i, _, rfl⟩
    exact Subgroup.mem_sup_right (splitWeylGenerator_mem P i)
  apply top_unique
  rw [← splitParabolic_sup P]
  exact sup_le (h .arms) (h .central)

/-- A nonzero negative simple curve has the rank-one Bruhat expression in
the literal matrices, with a coroot word and the numbered Weyl involution. -/
theorem negativeRoot_factorization (P : Parameters) (hp : P.prime = 2)
    (i : Fin 4) (t : ExtensionField P) (ht : t ≠ 0) :
    negativeRoot P i t = positiveRoot P i t⁻¹ *
      torusWord P i (Units.mk0 t⁻¹ (inv_ne_zero ht)) * weylWord P i 1 *
        positiveRoot P i t⁻¹ := by
  let := rankOneExtensionCharTwo P hp
  have hx : positiveRoot P i t⁻¹ * positiveRoot P i t⁻¹ = 1 := by
    rw [← positiveRoot_add, CharTwo.add_self_eq_zero t⁻¹, positiveRoot_zero]
  have hn : weylWord P i 1 * weylWord P i 1 = 1 := by
    simpa only [pow_two] using weylWord_sq P hp i
  have hw : torusWord P i (Units.mk0 t⁻¹ (inv_ne_zero ht)) * weylWord P i 1 =
      weylWord P i t⁻¹ := by
    simp only [torusWord, Units.val_mk0, CharTwo.neg_eq, mul_assoc, hn, mul_one]
  calc
    negativeRoot P i t = positiveRoot P i t⁻¹ * weylWord P i t⁻¹ *
        positiveRoot P i t⁻¹ := by
      simp only [weylWord, inv_inv, CharTwo.neg_eq]
      simp only [← mul_assoc, hx, one_mul]
      rw [mul_assoc, hx, mul_one]
    _ = positiveRoot P i t⁻¹ *
        (torusWord P i (Units.mk0 t⁻¹ (inv_ne_zero ht)) * weylWord P i 1) *
          positiveRoot P i t⁻¹ := congrArg
      (fun x => positiveRoot P i t⁻¹ * x * positiveRoot P i t⁻¹) hw.symm
    _ = _ := (congrArg (fun x => x * positiveRoot P i t⁻¹)
      (mul_assoc (positiveRoot P i t⁻¹)
        (torusWord P i (Units.mk0 t⁻¹ (inv_ne_zero ht))) (weylWord P i 1))).symm

end Triality.Standard.ConcreteBruhat.SplitNormalForm
