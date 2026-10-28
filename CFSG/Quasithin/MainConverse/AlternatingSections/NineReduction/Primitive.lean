module

public import CFSG.Quasithin.MainConverse.AlternatingSections.NineReduction.Primitive.Affine
public import CFSG.Quasithin.MainConverse.AlternatingSections.NineReduction.Primitive.Outer
public import BenderSuzuki.MatrixGroups.PSL2
public import BenderSuzuki.External.Huppert.II.theorem_6_14
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# The primitive degree-nine structural reduction

Source obligation: Aschbacher–Smith, Theorem 0.1.2(3), condition K, printed
pp.4 and 482. The intended result states that a proper primitive subgroup
of A₉ is solvable or has a normal subgroup isomorphic to the actual PSL₂(8)
matrix model with solvable quotient.

The abelian-normal branch is proved in `Primitive.Affine`. The quotient
clause is proved in `Primitive.Outer` by Frattini's argument at seven. The
assembly below leaves two explicit mathematical prerequisites: existence of
a nonabelian simple normal subgroup when every abelian normal subgroup is
trivial, and identification of that simple subgroup with PSL₂(8).

This is a conditional reduction, not the unconditional primitive-subgroup
classification. The public name `primitive_subgroup_structure` is reserved
for final assembly after those two prerequisites have been discharged.
-/

namespace CFSG.Quasithin.MainConverse.NineReduction

open BenderSuzuki.MatrixGroups

private theorem seven_dvd_card_pslTwoEight :
    7 ∣ Nat.card (PSL2MatrixGroup (GaloisField 2 3)) := by
  have hcard := BenderSuzuki.External.huppert614_card_psl_mul_center
    (K := GaloisField 2 3)
  have hcenter := BenderSuzuki.External.huppert614_card_center_of_neg_one_eq_one
    (K := GaloisField 2 3) (CharTwo.neg_eq 1)
  rw [hcenter, mul_one, GaloisField.card 2 3 (by decide)] at hcard
  change 7 ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 3))
  rw [hcard]
  norm_num

/-- A normal copy of the actual PSL₂(8) has solvable quotient in degree nine. -/
public theorem quotient_solvable_of_normal_pslTwoEight
    (H : Subgroup (alternatingGroup (Fin 9)))
    (N : Subgroup H) [N.Normal]
    (e : N ≃* PSL2MatrixGroup (GaloisField 2 3)) : Group.IsSolvable (H ⧸ N) := by
  apply quotient_solvable_of_seven_dvd
    ((alternatingGroup (Fin 9)).subtype.comp H.subtype)
    ((alternatingGroup (Fin 9)).subtype_injective.comp H.subtype_injective) N
  rw [Nat.card_congr e.toEquiv]
  exact seven_dvd_card_pslTwoEight

/-- Conditional assembly from simple-normal-subgroup existence and actual model identification.
The affine and outer-quotient premises are discharged in this module's imports. -/
public theorem primitive_subgroup_structure_of_simple_normal_inputs
    (hsocle : ∀ H : Subgroup (alternatingGroup (Fin 9)),
      MulAction.IsPreprimitive H (Fin 9) →
      (∀ A : Subgroup H, A.Normal → IsMulCommutative A → A = ⊥) →
      ∃ N : Subgroup H, N.Normal ∧ IsSimpleGroup N ∧ ¬ IsMulCommutative N)
    (hrecognition : ∀ H : Subgroup (alternatingGroup (Fin 9)), H ≠ ⊤ →
      MulAction.IsPreprimitive H (Fin 9) →
      ∀ N : Subgroup H, N.Normal → IsSimpleGroup N → ¬ IsMulCommutative N →
        Nonempty (N ≃* PSL2MatrixGroup (GaloisField 2 3)))
    (H : Subgroup (alternatingGroup (Fin 9))) (hH : H ≠ ⊤)
    (hp : MulAction.IsPreprimitive H (Fin 9)) :
    Group.IsSolvable H ∨ ∃ (N : Subgroup H) (_ : N.Normal),
      Nonempty (N ≃* PSL2MatrixGroup (GaloisField 2 3)) ∧ Group.IsSolvable (H ⧸ N) := by
  by_cases hsolv : Group.IsSolvable H
  · exact Or.inl hsolv
  · have habel (A : Subgroup H) (hn : A.Normal) (ha : IsMulCommutative A) : A = ⊥ := by
      by_contra hA
      let := hn
      let := ha
      exact hsolv (solvable_of_abelian_normal hp A hA)
    obtain ⟨N, hn, hs, hna⟩ := hsocle H hp habel
    let := hn
    obtain ⟨e⟩ := hrecognition H hH hp N hn hs hna
    exact Or.inr ⟨N, hn, ⟨e⟩, quotient_solvable_of_normal_pslTwoEight H N e⟩

end CFSG.Quasithin.MainConverse.NineReduction
