module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.SourceFF.Natural
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.SourceFF.Parameters
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.SourceFF.TwistedExclusion

/-!
# Recognition of the SL₃ FF source action

The original faithful irreducible action supplies its scalar covering and the
absolute-module sieve. The half-field tensor alternative contradicts the
actual FF hypothesis, since its quadratic ratio is strictly greater than two.
The surviving natural or dual-natural model descends on the original
component; its normality supplies the ambient semilinear equation.

Source: Aschbacher–Smith, K.3.2 and K.3.2.1–4, printed pp.454–456.
This separate FF specialization leaves the cubic-ratio interfaces unchanged.
-/

public section
noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.SourceFF
open ChapterB.QuasisimpleSource ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition

universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V]
  [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
  {K : GroupClass.{u}} {L : Subgroup G} {B : BinaryField}

/-- The original source action with an actual offender constructs the
natural source input, with its exact component and ambient action. -/
theorem naturalSourceInput_of_ff (h : SourceHypothesis K ρ L)
    (C : LinearCover B 3 L) (eQ : L ⧸ center L ≃* PSL(3,B.Carrier))
    (hff : IsFFModule ρ) : Nonempty (Natural.SourceInput ρ L B 3 K) := by
  let := h.finite_module
  let := inflated_irreducible ρ C h.irreducible
  obtain ⟨hs, hn | ht⟩ := absolute_models h C eQ
  · exact naturalSourceInput_of_absolute h C hn.1 hn.2.2
  · exact (TwistedExclusion.not_twisted_of_ff h C eQ hff hs ht.1 ht.2.2).elim

/-- The central quotient alone supplies the covering needed by FF
recognition; no covering or absolute-model premise remains. -/
theorem naturalSourceInput_of_quotient_ff (h : SourceHypothesis K ρ L)
    (eQ : L ⧸ center L ≃* PSL(3,B.Carrier)) (hff : IsFFModule ρ) :
    Nonempty (Natural.SourceInput ρ L B 3 K) := by
  obtain ⟨C, _⟩ := exists_linearCover h B eQ
  exact naturalSourceInput_of_ff h C eQ hff

end CFSG.Quasithin.ChapterK.Linear.Recognition.SourceFF
