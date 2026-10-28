module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesTwoFour.OrbitActions.Support

/-!
# Shared subexpressions of the literal Fischer words

Multiplication and inversion share the common subwords of nodes 3 through 14.
The comparison lemmas below are ordinary group equalities, checked in Lean.
Only the definitional involutivity of `aPerm` is used to identify its inverse.
Reproduce with `source/generate.py`; source: the retained ATLAS word program
`Fi23InFi24Prime/source/faithfulness/nodes.json`, GLS3 Table 5.3v.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesTwoFour.OrbitActions

def p0 : Ambient := aPerm

def p1 : Ambient := bPerm

def p2 : Ambient := p1 * p0

def p3 : Ambient := p2 * p2

def p4 : Ambient := p1 * p2

def p5 : Ambient := p1 * p3

def p6 : Ambient := p4 * p5

def p7 : Ambient := p6 * p3

def p8 : Ambient := p4 * p7

def p9 : Ambient := p3 * p3

def p10 : Ambient := p0 * p3

def p11 : Ambient := p10 * p6

def p12 : Ambient := p11 * p2

def p13 : Ambient := p12 * p8

def p14 : Ambient := p13 * p2

def p15 : Ambient := p14 * p4

def p16 : Ambient := p5 * p8

def p17 : Ambient := p16 * p9

def p18 : Ambient := p17 * p4

def p19 : Ambient := p18 * p4

def p20 : Ambient := p0 * p8

def p21 : Ambient := p20 * p5

def p22 : Ambient := p21 * p9

def p23 : Ambient := p22 * p2

def p24 : Ambient := p6 * p6

def p25 : Ambient := p24 * p7

def p26 : Ambient := p25 * p4

def p27 : Ambient := p19⁻¹

def p28 : Ambient := p26⁻¹

def p29 : Ambient := p15 * p1

def p30 : Ambient := p29 * p27

def p31 : Ambient := p23 * p1

def p32 : Ambient := p31 * p28

private theorem a_inv : aPerm⁻¹ = aPerm := rfl

theorem word3_eq : p15 = Word.word3 aPerm bPerm := by
  simp only [p15, p14, p13, p12, p11, p10, p0, p3, p2, p1, p6, p4, p5, p8, p7, Word.word3, a_inv, mul_assoc]

theorem word4_eq : p19 = Word.word4 aPerm bPerm := by
  simp only [p19, p18, p17, p16, p5, p1, p3, p2, p0, p8, p4, p7, p6, p9, Word.word4, a_inv, mul_assoc]

theorem word6_eq : p23 = Word.word6 aPerm bPerm := by
  simp only [p23, p22, p21, p20, p0, p8, p4, p1, p2, p7, p6, p5, p3, p9, Word.word6, a_inv, mul_assoc]

theorem word7_eq : p26 = Word.word7 aPerm bPerm := by
  simp only [p26, p25, p24, p6, p4, p1, p2, p0, p5, p3, p7, Word.word7, a_inv, mul_assoc]

theorem word5_eq : p30 = Word.word5 aPerm bPerm := by
  simp only [p30, p29, word3_eq, p1, p27, word4_eq, Word.word5, mul_assoc]

theorem word8_eq : p32 = Word.word8 aPerm bPerm := by
  simp only [p32, p31, word6_eq, p1, p28, word7_eq, Word.word8, mul_assoc]

end Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesTwoFour.OrbitActions
