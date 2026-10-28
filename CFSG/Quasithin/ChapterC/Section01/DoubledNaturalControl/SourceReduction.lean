module

public import CFSG.Quasithin.ChapterC.Section01.DoubledNaturalControl.SourceReduction.Contracts
public import CFSG.Quasithin.ChapterC.Section01.DoubledNaturalControl.SourceReduction.Offenders
public import CFSG.Quasithin.ChapterC.Section01.DoubledNaturalControl.SourceReduction.BaumannFamily

/-!
# The doubled-natural source reduction

From the original marked doubled-natural source, the maximum-elementary
comparison produces either a nontrivial characteristic subgroup of Baum(R)
normal in K, or the full plane-radical Thompson image. In the second case,
three actual component conjugates supply every premise of Baumann's argument.
The structural construction then gives the genuine MS input on
J = L ⊔ Baum(R), its explicit odd-index radical witness, and the transported
quotient and doubled-natural module markings.

No extra geometric or MS premise remains in `SourceData.reduce`. The later
commutator-core rigidity argument is separate from this source reduction.

Source: Aschbacher--Smith, C.1.37, printed pp.141--143, and B.2.18,
printed pp.80--81 of the combined 1 March 2004 manuscript.
-/

public section

namespace CFSG.Quasithin.ChapterC.DoubledNaturalControl.SourceReduction
open Subgroup Theory.GroupTheory
universe u
variable {K : Type u} [Group K] [Finite K]
  {κ : GroupClass.{u}} {L P U : Subgroup K} [L.Normal] [U.Normal]
  {T : Sylow 2 K}

/-- The unconditional doubled-natural source reduction. The first alternative
is the literal characteristic obstruction in K; the second constructs all
MS hypotheses and preserves the specified quotient and module coordinates. -/
theorem SourceData.reduce (d : SourceData κ L P U T) :
    (∃ C : Subgroup (B P), C.Characteristic ∧ C ≠ ⊥ ∧
      (C.map (B P).subtype).Normal) ∨ Nonempty (ReductionData d) := by
  classical
  by_cases hno : CharacteristicObstruction P
  · exact Or.inl hno
  · obtain hobs | ho := d.offender_reduction
    · exact (hno hobs).elim
    · obtain ⟨hf⟩ := d.baumann_family ho
      exact Or.inr ⟨d.reduction_of_geometry hno ho hf⟩

end CFSG.Quasithin.ChapterC.DoubledNaturalControl.SourceReduction
