module

public import CFSG.Quasithin.ChapterA.Section02.Sporadic
public import Theory.SpecificGroups.Alternating.ThreeRank
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionWords
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionAlternatingQuotient
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.Basic
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.AlternatingQuotient

/-!
# Alternating sections for the Lyons and Thompson exclusions

GLS3's involution tables give 2.A₁₁ in Lyons and 2^{1+8}.A₉ in Thompson.
Both alternating quotients are nonabelian simple and have 3-rank at least
three, contradicting the bound of A.2.15(2) once smaller-section induction
is supplied by the A.2.19 owner.

Both sections are constructed unconditionally in the fixed matrix carriers.
The literal Lyons word subgroup acts on eleven stars in a certified matrix
orbit; the Thompson word subgroup acts on nine certified four-spaces. These
actions give the surjective maps to A₁₁ and A₉. The checked involution and
commutation certificates place their domains in the respective centralizers.
The kernels are normal in these domains; no splitting or ambient simplicity
or order certificate is needed. The A.2.19 owner retains the smaller-section
induction needed to apply the rank obstructions.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
A.2.15 and A.2.19, printed pp. 37--41; GLS3, section 5.3, the Lyons table
(printed p. 278) and Table 5.3x (Thompson).
-/

namespace CFSG.Quasithin.ChapterA

/-- A quotient map from the specified Lyons word subgroup gives the desired
section; the involution and containment require no further assumptions. -/
public def lyonsA11SectionOfSurjective
    (f : Lyons.SimplicityCertificate.involutionLocalSubgroup →*
      alternatingGroup (Fin 11)) (hf : Function.Surjective f) :
    InvolutionCentralizerQuotientData Lyons.LyonsGroup (alternatingGroup (Fin 11)) where
  involution := Lyons.SimplicityCertificate.involutionLocalT
  involution_order := Lyons.SimplicityCertificate.orderOf_involutionLocalT
  numerator := Lyons.SimplicityCertificate.involutionLocalSubgroup
  centralizes := Lyons.SimplicityCertificate.involutionLocalSubgroup_le_centralizer_certified
  quotientMap := f
  surjective := hf

/-- The actual A₁₁ quotient section in the centralizer of the certified Lyons
involution. The matrix-orbit construction discharges the adapter's surjection
premise without any additional hypothesis. -/
public noncomputable def lyonsA11Section :
    InvolutionCentralizerQuotientData Lyons.LyonsGroup (alternatingGroup (Fin 11)) :=
  lyonsA11SectionOfSurjective Lyons.SimplicityCertificate.AlternatingQuotient.quotient
    Lyons.SimplicityCertificate.AlternatingQuotient.quotient_surjective

/-- The actual A₉ quotient section in the centralizer of the standard Thompson
involution, from the literal max3 words and their certified four-space action. -/
public noncomputable def thompsonA9Section :
    InvolutionCentralizerQuotientData Thompson.Model (alternatingGroup (Fin 9)) where
  involution := Thompson.generatorA
  involution_order := Thompson.InvolutionCentralizer.orderOf_generatorA
  numerator := Thompson.InvolutionCentralizer.AlternatingQuotient.wordSubgroup
  centralizes := Thompson.InvolutionCentralizer.AlternatingQuotient.wordSubgroup_le_centralizer
  quotientMap := Thompson.InvolutionCentralizer.AlternatingQuotient.quotientHom
  surjective := Thompson.InvolutionCentralizer.AlternatingQuotient.quotientHom_surjective

public theorem lyonsA11_simple : IsSimpleGroup (alternatingGroup (Fin 11)) :=
  alternatingGroup.isSimpleGroup (by simp)

public theorem thompsonA9_simple : IsSimpleGroup (alternatingGroup (Fin 9)) :=
  alternatingGroup.isSimpleGroup (by simp)

public theorem lyonsA11_nonabelian : ¬ IsMulCommutative (alternatingGroup (Fin 11)) := by
  intro h
  have := alternatingGroup.isMulCommutative_iff_card_le_three.mp h
  simp at this

public theorem thompsonA9_nonabelian : ¬ IsMulCommutative (alternatingGroup (Fin 9)) := by
  intro h
  have := alternatingGroup.isMulCommutative_iff_card_le_three.mp h
  simp at this

/-- The numerical obstruction needed by A.2.15(2) for the Lyons section. -/
public theorem lyonsA11_primeRank_three_gt_two :
    2 < primeRank 3 (alternatingGroup (Fin 11)) :=
  lt_of_lt_of_le (by decide) (alternatingGroup.ThreeRank.three_le_primeRank (by decide))

/-- The numerical obstruction needed by A.2.15(2) for the Thompson section. -/
public theorem thompsonA9_primeRank_three_gt_two :
    2 < primeRank 3 (alternatingGroup (Fin 9)) :=
  lt_of_lt_of_le (by decide) (alternatingGroup.ThreeRank.three_le_primeRank (by decide))

end CFSG.Quasithin.ChapterA
