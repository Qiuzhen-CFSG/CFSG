module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.PowerFusion.Coverage.Base
import Mathlib.Tactic.FinCases

/-!
# Exponent of the transported four-point fixer

Every carrier element fixing 0 has normal form `(0,i,j,k)`. Checking its
images at 78, 36 and 84 shows that fixing these three additional points forces
its sixth power to be one. The check uses the certified four-point base, so
only four images of each sixth power are needed. Separate 96-element rows
bound kernel reduction memory, with sequential declaration elaboration.

Source: retained ATLAS `J2G1-p100B0` normal forms; attribution and the
reproduction diagnostic are in `SevenCentralizer/source/README.md`.
-/

namespace Sporadic.LeechRelated.J2.PowerFusionCertificate.SevenCentralizerCertificates
open GeneratorPair.SecondOrbitCertificate ExceptionalParabolics.FirstParabolic.OrderData

set_option Elab.async false

private def Row (i : Fin 63) : Prop := ∀ j : Fin 24, ∀ k : Fin 4,
  let p := normalForm (0, i, j, k)
  p 78 = 78 → p 36 = 36 → p 84 = 84 →
  ∀ x : Fin 4, (p ^ 6) (x.castLE (by decide)) = x.castLE (by decide)

private theorem row00 : Row 0 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row01 : Row 1 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row02 : Row 2 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row03 : Row 3 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row04 : Row 4 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row05 : Row 5 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row06 : Row 6 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row07 : Row 7 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row08 : Row 8 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row09 : Row 9 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row10 : Row 10 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row11 : Row 11 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row12 : Row 12 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row13 : Row 13 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row14 : Row 14 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row15 : Row 15 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row16 : Row 16 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row17 : Row 17 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row18 : Row 18 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row19 : Row 19 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row20 : Row 20 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row21 : Row 21 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row22 : Row 22 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row23 : Row 23 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row24 : Row 24 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row25 : Row 25 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row26 : Row 26 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row27 : Row 27 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row28 : Row 28 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row29 : Row 29 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row30 : Row 30 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row31 : Row 31 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row32 : Row 32 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row33 : Row 33 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row34 : Row 34 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row35 : Row 35 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row36 : Row 36 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row37 : Row 37 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row38 : Row 38 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row39 : Row 39 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row40 : Row 40 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row41 : Row 41 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row42 : Row 42 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row43 : Row 43 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row44 : Row 44 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row45 : Row 45 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row46 : Row 46 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row47 : Row 47 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row48 : Row 48 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row49 : Row 49 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row50 : Row 50 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row51 : Row 51 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row52 : Row 52 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row53 : Row 53 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row54 : Row 54 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row55 : Row 55 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row56 : Row 56 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row57 : Row 57 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row58 : Row 58 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row59 : Row 59 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row60 : Row 60 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row61 : Row 61 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row62 : Row 62 := by
  unfold Row
  apply allFin
  decide +kernel

private theorem row_check (i : Fin 63) : Row i := by
  fin_cases i
  · exact row00
  · exact row01
  · exact row02
  · exact row03
  · exact row04
  · exact row05
  · exact row06
  · exact row07
  · exact row08
  · exact row09
  · exact row10
  · exact row11
  · exact row12
  · exact row13
  · exact row14
  · exact row15
  · exact row16
  · exact row17
  · exact row18
  · exact row19
  · exact row20
  · exact row21
  · exact row22
  · exact row23
  · exact row24
  · exact row25
  · exact row26
  · exact row27
  · exact row28
  · exact row29
  · exact row30
  · exact row31
  · exact row32
  · exact row33
  · exact row34
  · exact row35
  · exact row36
  · exact row37
  · exact row38
  · exact row39
  · exact row40
  · exact row41
  · exact row42
  · exact row43
  · exact row44
  · exact row45
  · exact row46
  · exact row47
  · exact row48
  · exact row49
  · exact row50
  · exact row51
  · exact row52
  · exact row53
  · exact row54
  · exact row55
  · exact row56
  · exact row57
  · exact row58
  · exact row59
  · exact row60
  · exact row61
  · exact row62

/-- The literal carrier's pointwise fixer of 0, 78, 36 and 84 has exponent
 dividing six. No enumeration or membership premise remains. -/
public theorem transformed_fixer_pow_six (g : Carrier)
    (h0 : inclusion g 0 = 0) (h78 : inclusion g 78 = 78)
    (h36 : inclusion g 36 = 36) (h84 : inclusion g 84 = 84) : g ^ 6 = 1 := by
  obtain ⟨⟨i₀, i₁, i₂, i₃⟩, rfl⟩ := element_surjective g
  have he := congrArg decode0 h0
  simp only [inclusion_element, normalForm, Equiv.Perm.mul_apply,
    rep3_fix0, rep2_fix0, rep1_fix0, decode0_spec] at he
  have hi : i₀ = 0 := he
  subst i₀
  apply carrier_ext_base
  exact row_check i₁ i₂ i₃ h78 h36 h84

end Sporadic.LeechRelated.J2.PowerFusionCertificate.SevenCentralizerCertificates
