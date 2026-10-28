module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.ActorGeometry
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.Models
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.EscapeTransport
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.Noninvolutory.RankTwo
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.InnerPlacement

/-!
# Quadratic field-image extensions without field involutions

The actor calculation proves actual self-centrality and tau equality for
four-groups in the literal PSL₂ kernel. The local assembly transports the
prime-square PSL₂ placement calculation to this extension and verifies all
intrinsic E1 conditions. The inner placement remains an explicit premise
of the transport lemma `Noninvolutory.largeFamilyEscape_of_inner_geometry`;
here `InnerPlacement.concreteLocalGeometryAt` discharges it. Thus every
proper Sylow overgroup containing the weak-closure normalizer admits an
escaping E1 member, under exactly the quadratic no-field-involution
hypotheses. The construction includes p = 3 and p = 5 and requires no
complement or semilinear local-model exhaustion.

`largeFamilyEscape` supplies the exact `hnonsplit` input of
`FieldWitnesses.largeFamilyEscape_of_involution_cases`.
`largeFamilyEscape_of_no_field_involutions` additionally derives the literal
kernel identification, so only the original field-image hypotheses remain.

Source: Aschbacher--Smith, E.1.1--2 and E.1.14(6), printed pp.209--210 and 214.
-/

public section

open Subgroup GorensteinWalter

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.Noninvolutory

/-- The quadratic branch without field involutions has genuine local E1
witnesses outside every proper overgroup of the Sylow and weak-closure
normalizer. The inner placement, ambient tau and intrinsic quotient
conditions are all discharged. -/
theorem largeFamilyEscape
    {F : Type*} [Field F] [Finite F] {p : ℕ}
    (hp : p.Prime) (hodd : Odd p) (hF : Nat.card F = p ^ 2)
    (hlarge : 5 < p ^ 2) (S : Subgroup (PGammaL2 F)) [Finite S]
    (hS : pGammaL2PSLRange F ≤ S)
    (hindex : (pGammaL2LinearKernel F S).index = 2)
    (hkernel : pGammaL2LinearKernel F S = (pGammaL2PSLRange F).subgroupOf S)
    (hnofield : ∀ x : S, orderOf x = 2 → pGammaL2FieldProjection F S x = 1) :
    ∀ T : Sylow 2 S, LargeFamilyEscapeAt T :=
  largeFamilyEscape_of_inner_geometry hp hodd hF hlarge S hS hindex hkernel hnofield
    (LinearWitnesses.InnerPlacement.concreteLocalGeometryAt hp hodd hlarge hF)

/-- Escape from the original no-field-involution hypotheses alone. The
literal kernel equality needed by the local geometry follows from the
index-two field image and the absence of field involutions. -/
theorem largeFamilyEscape_of_no_field_involutions
    {F : Type*} [Field F] [Finite F] {p : ℕ}
    (hp : p.Prime) (hodd : Odd p) (hF : Nat.card F = p ^ 2)
    (hlarge : 5 < p ^ 2) (S : Subgroup (PGammaL2 F)) [Finite S]
    (hS : pGammaL2PSLRange F ≤ S)
    (hindex : (pGammaL2LinearKernel F S).index = 2)
    (hnofield : ∀ x : S, orderOf x = 2 → pGammaL2FieldProjection F S x = 1) :
    ∀ T : Sylow 2 S, LargeFamilyEscapeAt T :=
  largeFamilyEscape hp hodd hF hlarge S hS hindex
    (linearKernel_eq_inner_of_no_field_involutions hp hodd hF S hS hindex hnofield)
    hnofield

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.Noninvolutory
