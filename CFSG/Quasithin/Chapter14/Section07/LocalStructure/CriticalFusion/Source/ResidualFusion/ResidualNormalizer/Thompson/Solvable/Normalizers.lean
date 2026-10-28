module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.Thompson.Solvable.Source
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.PlaneNoncentralitySource
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.TripleCore.LeftChiefFactors.SourceMarking

/-!
# Source normalizer equality in the solvable Thompson branch

The original 13.3.2 module implication supplies the point commutator.
The natural parabolic coordinates supply a compatible upper marking after
an allowed change of coordinates, retaining every ambient subgroup.
The proved solvable Thompson argument therefore makes the actual section
centralizer a two-group. The original automorphism correction then gives
N_G(K)=H, without a factorization, quotient or marking premise.

The distinct earlier 14.7.10 and 14.7.31 source implications remain explicit.
The nonsolvable Thompson branch remains with the component-module argument.
Source: Aschbacher–Smith, 14.7.67(4), printed pp.1070–1071.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 ResidualNormalizer
open Rechoice.Goldschmidt
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

/-- Literal 14.7.67(4) in the solvable case, with the marking, point
commutator, rank bound and B.2.16 all constructed from their source inputs. -/
theorem Data.normalizer_K_eq_H_of_solvable_source
    (d : Data T L V F W)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u})
    (earlier1332 : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
    (baumannAlternative : LocalControl.Earlier14710.{u})
    (weakClosure : Theorem14731.{u})
    (hsol : Group.IsSolvable (J L F)) : normalizer (K F : Set G) = F.H := by
  let d' := LeftChiefFactors.BorelRefinements.upperRemark d structural
  have mark := LeftChiefFactors.BorelRefinements.upperRemark_upperMarking d structural
  have hcomm := d'.U_core_commutator_eq_point_of_source1332 earlier1332 structural uniqueness
  have hD := d'.residual_D_twoGroup_of_solvable_source structural uniqueness
    baumannAlternative weakClosure mark hcomm hsol
  exact d.normalizer_K_eq_H_of_sectionCentralizer_twoGroup d.normalizer_K_eq_sup_D_T hD

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
