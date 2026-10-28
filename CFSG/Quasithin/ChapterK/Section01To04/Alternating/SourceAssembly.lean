module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.SourceFF
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.NaturalOffenders
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.SevenFourOffenders
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.HexacodeOffenders

/-!
# The alternating source branch of B.4.2

The original irreducible binary action and its offender now construct the
natural, four-dimensional A₇, or hexacode representation, including the marked
ambient extension. The completed offender calculations on those same models
then give all corresponding B.4.2 clauses on the original action. The inner
natural A₇ case has ratio 3/2 and is excluded by the actual FF hypothesis.

The direct source application constructs the cubic-ratio bound internally
from the given member of P(G,V). Its only family hypothesis is the supplied
central-quotient alternative A₆ or A₇; the B.4 dispatcher supplies that
alternative from the source simple-group catalogue.

Source: Aschbacher–Smith, B.4.2 and K.1–K.1.3, printed pp.86 and 452–453.
The hexacode offender description retains F₄ vector planes of dimension two.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory

namespace CFSG.Quasithin.ChapterK.Alternating

universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) {K : GroupClass.{u}} {L : Subgroup G}

/-- The completed model calculations apply to the same recognized source
action and include both ratios in the non-FF natural A₇ case. -/
theorem conclusion_of_recognized (h : Input ρ K L)
    (hr : RecognizedAction ρ L) : Conclusion ρ L := by
  cases hr with
  | six a => exact sixNatural_conclusion a
  | sevenNatural a => exact sevenNaturalAction_conclusion a
  | sevenFour hL a => exact sevenFour_conclusion ρ h hL a
  | tripleSix a => exact HexacodeOffenders.conclusion a

/-- All alternating B.4.2 action and offender clauses follow from the
original Input and an actual offender, without a recognition premise. -/
theorem source_of_ff_input (h : Input ρ K L) (hff : IsFFModule ρ) :
    RecognizedAction ρ L ∧
      ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase
        ρ L (offenderSubgroup ρ) := by
  have hr := recognition_of_ff ρ h hff
  have hc := conclusion_of_recognized ρ h hr
  cases hc with
  | ff _ hs => exact ⟨hr, hs⟩
  | sevenNatural _ _ hq _ =>
    have hle := (isFFModule_iff_quadraticRatio_le_one ρ).mp hff
    rw [hq] at hle
    rw [ENNReal.div_le_iff (by norm_num) (by simp), one_mul] at hle
    norm_num at hle

/-- Direct B.4.2 application on its literal subgroup L and member A of
P(G,V). The action equivalence, ambient marking, offender family and ratio
are all outputs; no module recognition or degree estimate is assumed. -/
theorem source_of_bestOffender
    (hsqtk : IsSQTK K G) (hfit : L = generalizedFitting G)
    (hquasi : IsQuasisimple L) (hfaith : Function.Injective ρ)
    (hirr : IsIrreducible (ρ.comp L.subtype))
    (hquot : Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7)))
    (A : Subgroup G) (hA : IsBestOffender ρ A) :
    RecognizedAction ρ L ∧
      ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase
        ρ L (offenderSubgroup ρ) := by
  have hff : IsFFModule ρ := ⟨A, hA.isOffender ρ⟩
  have hc : cubicRatio ρ ≤ 2 :=
    ((isFFModule_iff_cubicRatio_le_one ρ).mp hff).trans (by norm_num)
  exact source_of_ff_input ρ
    ⟨hsqtk, hfit, hquasi, hfaith, hirr, hc, hquot⟩ hff

end CFSG.Quasithin.ChapterK.Alternating
