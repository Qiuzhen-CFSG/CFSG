module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Actions


/-!
# The matrix-generation contract for the sharp chief-section bound

The intrinsic route to B.5.9's inequality (!) needs generation of the actual
SL₃(F) by three conjugates of any nonidentity involution. This declaration
only specifies that group-theoretic prerequisite; it does not prove it.
The conditional consumer is `irreducible_fixedCodim_lower_of_generation`
in the parent `FixedCodimension` module. Its proof uses the already proved
3m minimum dimension and contains no natural marking for arbitrary factors.

Source motivation: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.9, printed p.108. The generation route is an alternative proof of the
local fixed-codimension estimate.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure
open QuasisimpleSource
set_option backward.isDefEq.respectTransparency false

/-- The group-theoretic input for the intrinsic codimension route. This is a
contract to be proved for SL₃(F), not a local rank or classification assumption. -/
def ThreeInvolutionGeneration (F : BinaryField) : Prop :=
  ∀ t : Matrix.SpecialLinearGroup (Fin 3) F.Carrier, t ^ 2 = 1 → t ≠ 1 →
    ∃ g h, zpowers t ⊔ zpowers (g * t * g⁻¹) ⊔ zpowers (h * t * h⁻¹) = ⊤


end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure
