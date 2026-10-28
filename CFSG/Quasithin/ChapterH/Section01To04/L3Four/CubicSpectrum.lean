module

public import CFSG.Quasithin.ChapterH.Section01To04.L3Four.CubicSpectrum.Definitions
public import CFSG.Quasithin.ChapterH.Section01To04.L3Four.CubicSpectrum.Reduction
public import Theory.SpecificGroups.PSL3Four.FieldExtension.Basic

/-!+# The source application of the cubic displacement calculation

This application uses the concrete PSL₃(4) carrier, its actual isomorphism
with the generalized Fitting subgroup, and the faithful original action.
The three word-rank calculations remain explicit until the spectral producers
are assembled. Thus this module currently proves a conditional reduction,
not the unconditional cubic bound or H.4.7's involution assertion.

Source: Aschbacher–Smith H.4.7, refs/quasithin.pdf, printed pp.382–383.
-/

public section

open Representation Representation.SL3.BinaryDefiningFactors Theory.GroupTheory
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
  (SplittingField)
namespace CFSG.Quasithin.ChapterH.Section01To04.L3Four.CubicSpectrum

variable {M V : Type*} [Group M] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- The literal H.4.7 component application, conditional only on the three
absolute calculations for the genuine cover representation. -/
theorem source_psl3Four_cubic_displacement_of_word_ranks
    (e : Matrix.PSL3Four.PSL ≃* generalizedFitting M)
    (ρ : Representation (ZMod 2) M V)
    [IsIrreducible (ρ.comp (generalizedFitting M).subtype)] (hρ : Function.Injective ρ)
    (hdim : Module.finrank (ZMod 2) V ≠ 9)
    (hcalc : ∀ (g : Matrix.PSL3Four.SL),
      orderOf (QuotientGroup.mk' (Subgroup.center Matrix.PSL3Four.SL) g) = 3 →
      ∀ ι : Matrix.PSL3Four.F →+* SplittingField (coverRep e ρ),
      Module.finrank (SplittingField (coverRep e ρ))
        (LinearMap.range (wordRep ι [.adjoint,.trivial] g - 1)) = 6 ∧
      Module.finrank (SplittingField (coverRep e ρ))
        (LinearMap.range (wordRep ι [.trivial,.adjoint] g - 1)) = 6 ∧
      Module.finrank (SplittingField (coverRep e ρ))
        (LinearMap.range (wordRep ι [.adjoint,.adjoint] g - 1)) = 42)
    (x : M) (hx : x ∈ generalizedFitting M) (horder : orderOf x = 3) :
    12 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ x - 1)) := by
  exact source_displacement_of_word_ranks Matrix.PSL3Four.card_F e ρ hρ hdim hcalc
    ⟨x,hx⟩ ((Subgroup.orderOf_mk x hx).trans horder)

end CFSG.Quasithin.ChapterH.Section01To04.L3Four.CubicSpectrum
