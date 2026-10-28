module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.MathieuTwentyFourStabilizer
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.MathieuLocalSections

/-!
# Inner stabilizer action on a local A₈ section in M₂₄

The proved octad geometry identifies every source-local L₄(2) section
with an E₁₆-by-L₄(2) extension. Its odd index in M₂₄ then gives inner
stabilizer action. Both the local family and the intrinsic two-core quotient
are transported through the same ambient equivalence.

Source: Aschbacher–Smith A.3.12(14), used in15.3.32(3), printed p.1133.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.MathieuTwentyFourStabilizer
variable {Q : Type*} [Group Q] [Finite Q]

/-- The source-local hypothesis itself discharges the extension premise. -/
theorem twoStabilizerActsInner_of_local_section
    (e : Q ≃* Sporadic.Mathieu.M24) (A : Subgroup Q) (S : Sylow 2 Q)
    (hsection : ClassicalGroup.IsPSL (XiQuotient A) 4 2)
    (hlocal : A ∈ ChapterA.Section03.localCComponents S) :
    TwoStabilizerActsInner A := by
  apply TwoStabilizerActsInner.of_map e
  have hsection' : ClassicalGroup.IsPSL (XiQuotient (A.map e.toMonoidHom)) 4 2 := by
    let f := e.subgroupMap A
    exact hsection.of_mulEquiv (QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).symm
  let T := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hlocal' : A.map e.toMonoidHom ∈ ChapterA.Section03.localCComponents T := by
    let : Group.IsSolvable e.toMonoidHom.ker := by
      rw [e.toMonoidHom.ker_eq_bot e.injective]
      infer_instance
    exact Section02.localCComponents_map_of_solvable_ker hlocal e.toMonoidHom
  exact twoStabilizerActsInner (MulEquiv.refl _) _
    (JankoFourStabilizer.mathieuLocalFourExtension _ T hsection' hlocal')

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.MathieuTwentyFourStabilizer
