module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.DihedralPSL2

/-!
# The actual square-field extension in the split-sixteen source branch

The square-field component can have defining prime congruent to either three
or five modulo eight. The record keeps the actual Frobenius involution,
its conjugation action, generation and the original common Sylow. It makes no
assertion that every original local pair has two symmetric-four factors.
The original row (8) remains unchanged; a genuine prime-three conclusion
recovers its field-extension record for the terminal comparison.

Source: Aschbacher–Smith, F.6.18(8), printed pp.309–310, retaining the
square-field alternatives supplied by the actual split-sixteen component.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
universe u
variable {D : Type u} [Group D] [Finite D]

structure SquareFieldExtensionRow (S : Sylow 2 D) where
  field : FieldParameter.{u}
  degree : field.degree = 2
  congruence : field.prime % 8 = 3 ∨ field.prime % 8 = 5
  componentEquiv : generalizedFitting D ≃* PSL(2,field.Carrier)
  quasisimple : IsQuasisimple (generalizedFitting D)
  sylow : Nonempty (S ≃* (C 2 × DihedralGroup 4))
  automorphism : field.Carrier ≃+* field.Carrier
  frobenius : ∀ x, automorphism x = x ^ field.prime
  element : D
  involution : orderOf element = 2
  outside : element ∉ generalizedFitting D
  generated : generalizedFitting D ⊔ zpowers element = ⊤
  action : ∀ x : generalizedFitting D,
    ∃ y : generalizedFitting D,
      (y : D) = element * (x : D) * element⁻¹ ∧
      componentEquiv y = Theory.PSL2.OuterSolvable.projectiveFieldAutHom automorphism
        (componentEquiv x)

/-- A proved prime-three restriction recovers the original field record,
including its literal conjugation action. -/
def SquareFieldExtensionRow.toFieldExtension {S : Sylow 2 D}
    (r : SquareFieldExtensionRow S) (hp : r.field.prime = 3) : FieldExtensionRow (D := D) where
  field := r.field
  degree := r.degree
  congruence := by rw [hp]
  componentEquiv := r.componentEquiv
  automorphism := r.automorphism
  frobenius := r.frobenius
  element := r.element
  involution := r.involution
  outside := r.outside
  generated := r.generated
  action := r.action

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
