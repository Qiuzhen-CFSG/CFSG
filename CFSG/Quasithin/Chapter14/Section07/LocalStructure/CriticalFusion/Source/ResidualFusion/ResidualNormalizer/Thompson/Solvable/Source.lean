module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.Thompson.Solvable
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.Thompson.Solvable.Recognition
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.Thompson.Solvable.ThreeRank
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.LocalControl
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.SourceCompletion.ModuleSeparation
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Thompson.Application.Source.Complete

/-!
# The actual solvable Thompson branch of 14.7.67

The proved universal B.2.16 and the original three-rank bound construct the
S₃ equivalence on the literal quotient JR₁/O₂(DR₁). Module separation is
also proved from the original datum. The actual intersection and Sylow
bounds follow from the earlier structural and uniqueness theorems.

Consequently, in the solvable branch J(DR₁), the section centralizer D is
a two-group once the genuine earlier Baumann alternative 14.7.10 and
weak-closure theorem 14.7.31 are supplied. These two distinct source
implications remain explicit; neither is replaced by a factorization or
normalizer conclusion. The point commutator is the original 14.5.21 input.

Source: Aschbacher–Smith, 14.7.67(4), printed pp.1070–1071; B.2.16.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 Theory.GroupTheory ResidualNormalizer
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

namespace Data
variable (d : Data T L V F W)
include d

/-- The literal S₃ quotient with B.2.16 and the three-rank bound discharged. -/
theorem residual_thompsonJoin_quotient_symmetricThree_source
    (hsol : Group.IsSolvable (J L F))
    (hDM : D F ⊓ normalizer (L : Set G) ≤ (T : Subgroup G))
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    (hBaum : normalizer (ChapterB.baumann (F.Ri L 1) : Set G) ≤ normalizer (L : Set G))
    (hD : ¬ IsPGroup 2 (D F)) :
    Nonempty (JRQuotient L F ≃* Equiv.Perm (Fin 3)) :=
  d.residual_thompsonJoin_quotient_symmetricThree
    Chapter1.RadicalNormalizers.ThompsonSource.source_theoremB216 hsol
    d.residual_Y_threeRank_le_one hDM hSylow hBaum hD

/-- Complete solvable-branch application on the original datum, retaining
only the independent earlier source implications. -/
theorem residual_D_twoGroup_of_solvable_source
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u})
    (baumannAlternative : LocalControl.Earlier14710.{u})
    (weakClosure : Theorem14731.{u})
    (mark : Rechoice.LocalGeometry.Preparation.UpperMarking d)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (hsol : Group.IsSolvable (J L F)) : IsPGroup 2 (D F) := by
  by_contra hD
  obtain ⟨_,hDM,_,hSylow,hBaum⟩ := d.residual_local_control_of_point_commutator
    structural uniqueness baumannAlternative mark hcomm
  obtain ⟨e⟩ := d.residual_thompsonJoin_quotient_symmetricThree_source
    hsol hDM hSylow hBaum hD
  exact d.false_of_residual_thompson_quotient
    (Rechoice.SourceCompletion.moduleSeparation d) structural weakClosure
    hDM hSylow hBaum hD e

/-- The original solvable Thompson branch with 14.7.31 discharged. The independent
12.2.2, 1.2.7, 14.7.10 and point-commutator inputs retain their original scope. -/
theorem residual_D_twoGroup_of_solvable_source14731
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u})
    (baumannAlternative : LocalControl.Earlier14710.{u})
    (mark : Rechoice.LocalGeometry.Preparation.UpperMarking d)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (hsol : Group.IsSolvable (J L F)) : IsPGroup 2 (D F) :=
  d.residual_D_twoGroup_of_solvable_source structural uniqueness baumannAlternative
    (source_theorem14731 structural) mark hcomm hsol

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
