module
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure.LeviStructure.Blocks
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.GroupTheory.Commutator.PerfectLocalReduction

/-!
# Perfect normal subgroups of the hyperplane parabolic

A nontrivial perfect normal subgroup has nontrivial image in the simple SL4(2)
Levi quotient. Its image is therefore the entire Levi quotient, so its order
is divisible by five. The two-core is retained as the full quotient kernel.
Source: Aschbacher--Smith C.4.8 and 12.1.11.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure

private theorem simple_quotient_card_dvd
    {D S : Type*} [Group D] [Finite D] [Group S] [Finite S] [IsSimpleGroup S]
    (e : (D ⧸ pCore 2 D) ≃* S)
    (B : Subgroup D) [B.Normal] [Group.IsPerfect B] (hB : B ≠ ⊥) :
    Nat.card S ∣ Nat.card B := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 D))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let : (B.map q).Normal := Normal.map inferInstance q hq
  rcases (inferInstance : (B.map q).Normal).eq_bot_or_eq_top with hz | ht
  · have hker : q.ker = pCore 2 D := by
      rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    have hle : B ≤ pCore 2 D := by
      rw [←hker]
      exact (map_eq_bot_iff B).mp hz
    let : Group.IsNilpotent B := (pCore_isPGroup.to_le hle).isNilpotent
    let : Nontrivial B := B.nontrivial_iff_ne_bot.mpr hB
    exact (Group.IsPerfect.not_isSolvable B inferInstance).elim
  · have hdiv := B.card_map_dvd q
    simpa only [ht,Nat.card_congr Subgroup.topEquiv.toEquiv] using hdiv

/-- Every nontrivial perfect normal subgroup of the literal hyperplane
parabolic has a factor five in its order. -/
theorem five_dvd_card_of_normal_perfect
    (B : Subgroup (parabolic 4)) [B.Normal] [Group.IsPerfect B] (hB : B ≠ ⊥) :
    5 ∣ Nat.card B := by
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2)) :=
    Atlas.psl_simple_high_rank (F := ZMod 2) 4 (by decide)
  let : IsSimpleGroup SL(4,ZMod 2) :=
    (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide : 0 < 4)).symm.isSimpleGroup
  have hdiv := simple_quotient_card_dvd parabolicFourQuotientEquiv B hB
  have hc : Nat.card SL(4,ZMod 2) = 20160 := by
    rw [Nat.card_congr ((BinaryLinear.OuterCyclic.slEquivLinear 4).trans
      (BinaryLinear.OuterCyclic.matrixEquivLinear 4).symm).toEquiv,Matrix.card_GL_field]
    decide
  rw [hc] at hdiv
  exact (by decide : 5 ∣ 20160).trans hdiv

end Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure
