module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.Thompson.Solvable.Intermediate
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.Thompson.Solvable.Recognition.Quotients
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.Thompson.Solvable.Recognition.OldCore

/-!
# Solvable Thompson recognition for the residual normalizer

The intrinsic recognition gives J/O₂(J) ≃ S₃, m₃(J)=1, and
JR₁/O₂(JR₁) ≃ S₃ from the genuine universal B.2.16 and the source rank
bound. The point-centralizer and Baumann-normalizer arguments in OldCore
prove JR₁ = DR₁ and identify the old core O₂(DR₁), regarded inside JR₁,
with O₂(JR₁). Transporting the intrinsic equivalence across that equality
gives the literal JRQuotient required by the weak-closure argument.

The universal B.2.16 and the three-rank bound remain the explicit inputs
owned by qt-b-02 and qt-14-07-residual-thompson-three-rank. The subsequent
W₀ contradiction and discharge of those inputs remain with the solvable
branch assembly. No quotient identification, core equality or factor count
is assumed here.

Source: Aschbacher–Smith, 14.7.67(4), printed pp.1070–1071, combined
manuscript of 1 March 2004; B.2.16, printed p.79.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 Theory.GroupTheory ResidualNormalizer
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

namespace Data
variable (d : Data T L V F W)
include d

/-- The actual quotient JR₁/O₂(DR₁) is S₃. This discharges the quotient
premise of `false_of_residual_thompson_quotient`, using the literal old core. -/
theorem residual_thompsonJoin_quotient_symmetricThree
    (hB : Chapter1.RadicalNormalizers.ThompsonSource.TheoremB216.{u})
    (hsol : Group.IsSolvable (J L F)) (hr : primeRank 3 (Y L F) ≤ 1)
    (hDM : D F ⊓ normalizer (L : Set G) ≤ (T : Subgroup G))
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    (hBaum : normalizer (ChapterB.baumann (F.Ri L 1) : Set G) ≤ normalizer (L : Set G))
    (hD : ¬ IsPGroup 2 (D F)) :
    Nonempty (JRQuotient L F ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨e⟩ := d.residual_thompsonJoin_newCore_quotient_symmetricThree
    hB hsol hr hDM hSylow hBaum hD
  exact ⟨(QuotientGroup.quotientMulEquivOfEq
    (d.residual_thompsonJoin_coreInJR_eq hDM hSylow hBaum)).trans e⟩

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
