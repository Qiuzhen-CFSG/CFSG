module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.Reduction

/-!
# Independent inputs to the marked split normalizer

`LiftedFive` asks for the actual normal A₅ lifted into C_G(t), containing
E and X₁. Normality is relative to that centralizer. It assumes no splitting,
centralization, layer identification, core identification or normalizer model.

`CubicFourModel` asks for the independent recognition of the literal join
U X₃, retaining the actual embedding of its intrinsic two-core. Its producer
uses the frame's transitive cubic action on U. The splitting argument derives
the final marked E₄ × A₅ centralizer and A₄ × A₅ normalizer from these inputs.
Neither record asserts that its required witness exists.

Source: Aschbacher, *Sporadic Groups* (1994), 47.1(1), printed p.260.
-/

@[expose] public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer

variable {G : Type*} [Group G] [Finite G] {D : Seed G} {t : G}

/-- A normal A₅ in the literal centralizer, with the source Borel marking. -/
structure LiftedFive (F : LocalFrame D t) where
  K : Subgroup G
  le_centralizer : K ≤ involutionCentralizer t
  normal : (K.subgroupOf (involutionCentralizer t)).Normal
  equiv : K ≃* A5
  E_le : F.E ≤ K
  X1_le : F.X1 ≤ K

/-- The affine four-point recognition, retaining the intrinsic two-core. -/
structure CubicFourModel (F : LocalFrame D t) where
  equiv : (F.U ⊔ F.X3 : Subgroup G) ≃* A4
  core_eq : (pCore 2 A4).map
    ((F.U ⊔ F.X3).subtype.comp equiv.symm.toMonoidHom) = F.U

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer
