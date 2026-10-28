module
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Trio.FixedCommutators.Translations
public import Theory.GroupTheory.SolvableResidual
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Paired translations inside the intrinsic trio residual

The binary special linear quotient is perfect. Therefore a fixed-point-free
linear element lifts to the intrinsic solvable residual of the native trio
stabilizer. Its commutators with paired translations give every paired
translation. The solvable symmetric-three image of the residual is trivial,
so the residual fixes each octad. The intrinsic two-core also fixes the
parts, by its previously checked affine-kernel description.

Source: Aschbacher–Smith, H.15.6(1), printed p.401. All residuals here are
intrinsic solvable residuals; no two-residual or ambient normality is used.
-/

public section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.QuotientConstruction
open scoped Pointwise
namespace MathieuCode.TrioCalculation
noncomputable section

lemma standardAffineHom_fixes_octad (g : trioStabilizer standardTrio)
    (hg : (standardAffineHom g).1 = 1) (i : Fin 3) :
    g.val • standardTrioOctad i = standardTrioOctad i := by
  obtain ⟨t, ht⟩ := affineQuotient_spec affineCoverage g
  apply Finset.eq_of_subset_of_card_le ?_ (by simp)
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_smul_finset.mp hx
  obtain ⟨⟨j,v⟩, rfl⟩ := point.surjective y
  have hji : j = i := (point_mem_octad_iff j i v).mp hy
  subst j
  change g.val.val (point (i,v)) ∈ standardTrioOctad i
  rw [ht]
  change point ((standardAffineHom g).1 i, _) ∈ _
  rw [hg]
  exact point_mem_octad _ _

lemma standardTwoCore_fixes_octad (g : trioStabilizer standardTrio)
    (hg : g ∈ pCore 2 (trioStabilizer standardTrio)) (i : Fin 3) :
    g.val • standardTrioOctad i = standardTrioOctad i := by
  apply standardAffineHom_fixes_octad
  have he : standardAffineHom g = 1 := by
    rw [← standardAffineHom_ker] at hg
    exact hg
  exact congrArg Prod.fst he

private lemma symmetricThree_solvable : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
  let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
  apply Group.isSolvable_of_ker_le_range
    (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
  rw [Subgroup.range_subtype, ← alternatingGroup_eq_sign_ker]

lemma standardResidual_fixes_octad (g : trioStabilizer standardTrio)
    (hg : g ∈ Subgroup.solvableResidual (trioStabilizer standardTrio)) (i : Fin 3) :
    g.val • standardTrioOctad i = standardTrioOctad i := by
  apply standardAffineHom_fixes_octad
  let f := (MonoidHom.fst _ _).comp standardAffineHom
  have hm := Subgroup.map_solvableResidual_le f (Subgroup.mem_map_of_mem f hg)
  let := symmetricThree_solvable
  rw [Subgroup.solvableResidual_eq_bot] at hm
  exact hm

lemma pairedTranslation_mul (j : Fin 3) (u v : Vector) :
    pairedTranslation j u * pairedTranslation j v = pairedTranslation j (u + v) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro x
  obtain ⟨⟨i,w⟩, rfl⟩ := point.surjective x
  change (pairedTranslation j u).val.val ((pairedTranslation j v).val.val (point (i,w))) = _
  rw [pairedTranslation_point, pairedTranslation_point, pairedTranslation_point]
  by_cases hi : i = j
  · simp [hi]
  · simp [hi, add_assoc, add_comm v u]

lemma pairedTranslation_zero (j : Fin 3) : pairedTranslation j 0 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro x
  obtain ⟨⟨i,w⟩, rfl⟩ := point.surjective x
  change (pairedTranslation j 0).val.val (point (i,w)) = point (i,w)
  simp [pairedTranslation_point]

lemma pairedTranslation_inv (j : Fin 3) (v : Vector) :
    (pairedTranslation j v)⁻¹ = pairedTranslation j v := by
  apply inv_eq_of_mul_eq_one_right
  rw [pairedTranslation_mul, show v + v = 0 by ext k; exact CharTwo.add_self_eq_zero _,
    pairedTranslation_zero]

lemma pairedTranslation_conjugate (g : trioStabilizer standardTrio)
    (A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hg : standardAffineHom g = (1,A)) (j : Fin 3) (v : Vector) :
    g * pairedTranslation j v * g⁻¹ =
      pairedTranslation j (Matrix.SpecialLinearGroup.toLin' A v) := by
  apply (mul_right_cancel_iff (a := g)).mp
  rw [mul_assoc, inv_mul_cancel, mul_one]
  obtain ⟨t, ht⟩ := affineQuotient_spec affineCoverage g
  change HasAffineForm g (standardAffineHom g) t at ht
  rw [hg] at ht
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro x
  obtain ⟨⟨i,w⟩, rfl⟩ := point.surjective x
  change g.val.val ((pairedTranslation j v).val.val (point (i,w))) =
    (pairedTranslation j (Matrix.SpecialLinearGroup.toLin' A v)).val.val
      (g.val.val (point (i,w)))
  rw [pairedTranslation_point, ht, ht]
  change point (i, _) = (pairedTranslation j _).val.val (point (i, _))
  rw [pairedTranslation_point]
  by_cases hi : i = j
  · simp [hi]
  · simp [hi, map_add, add_right_comm]

private lemma slThree_perfect : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  let := Atlas.Comparisons.Exceptional.sl3Two_simple
  refine ⟨(IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (commutator (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) inferInstance).resolve_left ?_⟩
  intro h
  let := (commutator_eq_bot_iff _).mp h
  let : CommGroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    { (inferInstance : Group _) with mul_comm := IsMulCommutative.is_comm.comm }
  have hp := IsSimpleGroup.prime_card (α := Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
  rw [Atlas.Comparisons.Exceptional.sl3Two_card] at hp
  norm_num at hp

private def fixedFreeLinear : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  AffineLiftConstruction.linearCycle * AffineLiftConstruction.linearTransvection

private lemma fixedFreeLinear_displacements (v : Vector) :
    ∃ u : Vector, Matrix.SpecialLinearGroup.toLin' fixedFreeLinear u + u = v := by
  revert v
  decide +kernel

lemma pairedTranslation_mem_residual (j : Fin 3) (v : Vector) :
    pairedTranslation j v ∈ Subgroup.solvableResidual (trioStabilizer standardTrio) := by
  let A := fixedFreeLinear
  let := slThree_perfect
  have hA : (1,A) ∈ Subgroup.solvableResidual QuotientModel := by
    let f := MonoidHom.inr (Equiv.Perm (Fin 3)) (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    apply Subgroup.map_solvableResidual_le f
    apply Subgroup.mem_map_of_mem
    rw [Subgroup.solvableResidual_eq_top]
    exact Subgroup.mem_top _
  rw [← Subgroup.map_solvableResidual_eq standardAffineHom standardAffineHom_surjective] at hA
  obtain ⟨g,hg,hgA⟩ := hA
  obtain ⟨u,hu⟩ := fixedFreeLinear_displacements v
  have he : g * pairedTranslation j u * g⁻¹ * (pairedTranslation j u)⁻¹ =
      pairedTranslation j v := by
    rw [pairedTranslation_conjugate g A hgA, pairedTranslation_inv, pairedTranslation_mul]
    exact congrArg (pairedTranslation j) hu
  rw [← he, mul_assoc, mul_assoc]
  apply Subgroup.mul_mem _ hg
  exact (inferInstance : (Subgroup.solvableResidual (trioStabilizer standardTrio)).Normal).conj_mem
    g⁻¹ ((Subgroup.solvableResidual _).inv_mem hg) (pairedTranslation j u)

end
end MathieuCode.TrioCalculation
