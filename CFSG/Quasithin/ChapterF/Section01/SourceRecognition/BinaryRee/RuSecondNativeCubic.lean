module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.BinaryRee.RuSecondCubic
public import Theory.SpecificGroups.ReeTwo.ParabolicMarkedComparison.SecondCubic

/-!
# The source second core with the actual full-Ree cubic action

The earlier source theorem constructs X and F₂/A. The native root/reflection
cubic has proved order three. Cubic normalization now identifies the original
X conjugation on A with that exact native action, retaining the ambient formula.
The extension across the remaining quotient involution is a separate step.

Source: Aschbacher–Smith J.4.4–5, F.1.12, printed pp.441–442 and262–264.
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} {p : Plane d}

/-- Original source A and X realize the specified native cubic. -/
theorem SourceChoice.exists_A_native_cubic_marking (s : SourceChoice p)
    (B5 : Sylow 5 d.toTypeRuSetup.H) (hi : ∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    ∃(X : Sylow 3 p.parabolic)
      (e : p.A B5 ≃* ReeTwo.SylowModel.firstParabolicCore) (x : X),
      Nonempty (((p.F₂ B5 X) ⧸ (p.A B5).subgroupOf (p.F₂ B5 X)) ≃* Equiv.Perm (Fin 3)) ∧
      orderOf x=3 ∧ ∀a : ReeTwo.SylowModel.firstParabolicCore,
        (e.symm (ReeTwo.SylowModel.CubicAction.cubic a):G)=
          ((x:p.parabolic):G)*(e.symm a:G)*((x:p.parabolic):G)⁻¹ :=
  s.exists_A_cubic_marking B5 hi _ ReeTwo.SylowModel.CubicAction.cubic_order

end CFSG.Quasithin.ChapterJ.RuSubgroup
