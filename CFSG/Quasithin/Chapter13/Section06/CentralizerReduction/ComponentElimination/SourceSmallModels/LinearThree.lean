module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.FixedSpace
public import Theory.Representation.PSL3Two.ParabolicFixedFree

/-!
# The marked L₃(2) fixed-space calculation in 13.6.22

A chosen conjugation model identifies U/C_U(K) with the actual natural
three-space or its doubled module. When the image of the literal Lᵥ
contains O²(P) for the marked line parabolic, its fixed subgroup on U is
exactly C_U(K). Two-perfection then transports this equality to the
checked centralizer quotient used in the final paragraph.

The source branch must still construct the model and the placement of
Lᵥ from its invariant line and the C.1.34 alternatives. These are explicit
geometric premises here; no component is identified with the abelian module.
The central-action obstruction in 13.6.20 remains the separate
`SourceDoubledNatural.not_normalizes_splitPlane` calculation, used by the
containment owner before this source step.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, p.932.
-/

public section
open Subgroup Representation BinaryLinearThree
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels
variable {G : Type*} [_root_.Group G] {L K U : Subgroup G} {v : G}

/-- The single-natural action calculation, on the actual subgroup U. -/
theorem natural_centralizer_eq
    (m : ConjugationQuotientModel K U W) (hLK : Lv L v ≤ K)
    (hmark : residual lineParabolicSL ≤ ((Lv L v).subgroupOf K).map m.actor) :
    U ⊓ centralizer (Lv L v : Set G) = U ⊓ centralizer (K : Set G) := by
  apply m.centralizer_eq (Lv L v) hLK
  intro w hw
  apply ParabolicFixedFree.natural_fixed_eq_zero w
  intro g hg
  obtain ⟨k, hk, rfl⟩ := hmark hg
  exact hw ⟨k, hk⟩

/-- Two copies use one marking of K, rather than independent coordinates. -/
theorem doubled_centralizer_eq
    (m : ConjugationQuotientModel K U (W.prod W)) (hLK : Lv L v ≤ K)
    (hmark : residual lineParabolicSL ≤ ((Lv L v).subgroupOf K).map m.actor) :
    U ⊓ centralizer (Lv L v : Set G) = U ⊓ centralizer (K : Set G) := by
  apply m.centralizer_eq (Lv L v) hLK
  intro w hw
  apply ParabolicFixedFree.doubled_fixed_eq_zero w
  intro g hg
  obtain ⟨k, hk, rfl⟩ := hmark hg
  exact hw ⟨k, hk⟩

/-- Source application to C_G(v)/⟨v⟩ for a single natural module. -/
theorem natural_checked_centralizer_eq [Finite G]
    (m : ConjugationQuotientModel K U W) (hLK : Lv L v ≤ K) (hv : v ^ 2 = 1)
    (hmark : residual lineParabolicSL ≤ ((Lv L v).subgroupOf K).map m.actor) :
    checkedImage v U ⊓ centralizer (checkedImage v (Lv L v) : Set (Gcheck v)) =
      checkedImage v U ⊓ centralizer (checkedImage v K : Set (Gcheck v)) :=
  checked_centralizer_eq_of_ambient L K U v hLK hv (natural_centralizer_eq m hLK hmark)

/-- Source application to the same checked quotient for two natural summands. -/
theorem doubled_checked_centralizer_eq [Finite G]
    (m : ConjugationQuotientModel K U (W.prod W)) (hLK : Lv L v ≤ K) (hv : v ^ 2 = 1)
    (hmark : residual lineParabolicSL ≤ ((Lv L v).subgroupOf K).map m.actor) :
    checkedImage v U ⊓ centralizer (checkedImage v (Lv L v) : Set (Gcheck v)) =
      checkedImage v U ⊓ centralizer (checkedImage v K : Set (Gcheck v)) :=
  checked_centralizer_eq_of_ambient L K U v hLK hv (doubled_centralizer_eq m hLK hmark)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels
