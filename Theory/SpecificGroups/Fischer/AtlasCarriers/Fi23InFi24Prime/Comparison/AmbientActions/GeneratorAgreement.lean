module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.GeneratorAgreement.CycleData
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.GeneratorAgreement.Checker
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.GeneratorAgreement.Samples.A
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.GeneratorAgreement.Samples.B
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.GeneratorAgreement.SourceCertificates.A
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.GeneratorAgreement.SourceCertificates.B
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.GeneratorAgreement.ActionCertificates
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.WordEvaluation

/-!
# Source and local-action assembly for the packed Fi24' generators

Exact string decoding and disjoint support, together with local checks on each
short cycle and its complement, determine all four signed generator maps. The
signed interpretation then applies to the actual candidate words and label map
in `GeneratorAgreement.Application`. No group order, recognition, or stabilizer
identification is used.

The complete source/support and local-action certificates discharge every
premise of the four generator comparisons and `letterMap_correct`. The
conditional interfaces remain available for separate certificate applications.

Source: ATLAS F24G1-p306936B0.g1/.g2, retained with attribution in
AtlasCarriers/source/; the original cycle product is inverted by CycleEncoding.
The consumer is the Fi23 subgroup construction for GLS3 Table 5.3v.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient
open GeneratorAgreement

theorem aMap_correct_of_certificates
    (hs : SourceCertificate cycleBlocksA cyclesA maskA)
    (ha : ActionCertificate aMap aInvMap cyclesA maskA) (x : Fin 306936) :
    aMap x = generatorA x :=
  (signed_maps_correct cycleBlocksA cyclesA maskA aMap aInvMap hs ha).1 x

theorem aInvMap_correct_of_certificates
    (hs : SourceCertificate cycleBlocksA cyclesA maskA)
    (ha : ActionCertificate aMap aInvMap cyclesA maskA) (x : Fin 306936) :
    aInvMap x = generatorA⁻¹ x :=
  (signed_maps_correct cycleBlocksA cyclesA maskA aMap aInvMap hs ha).2 x

theorem bMap_correct_of_certificates
    (hs : SourceCertificate cycleBlocksB cyclesB maskB)
    (ha : ActionCertificate bMap bInvMap cyclesB maskB) (x : Fin 306936) :
    bMap x = generatorB x :=
  (signed_maps_correct cycleBlocksB cyclesB maskB bMap bInvMap hs ha).1 x

theorem bInvMap_correct_of_certificates
    (hs : SourceCertificate cycleBlocksB cyclesB maskB)
    (ha : ActionCertificate bMap bInvMap cyclesB maskB) (x : Fin 306936) :
    bInvMap x = generatorB⁻¹ x :=
  (signed_maps_correct cycleBlocksB cyclesB maskB bMap bInvMap hs ha).2 x

/-- The exact four signed comparisons discharge the word evaluator's premise. -/
theorem letterMap_correct_of_cycle_certificates
    (hsa : SourceCertificate cycleBlocksA cyclesA maskA)
    (hsb : SourceCertificate cycleBlocksB cyclesB maskB)
    (haa : ActionCertificate aMap aInvMap cyclesA maskA)
    (hab : ActionCertificate bMap bInvMap cyclesB maskB) :
    ∀ c x, letterMap c x = (letterValue c).val x :=
  letterMap_correct_of_generators
    (aMap_correct_of_certificates hsa haa) (bMap_correct_of_certificates hsb hab)
    (aInvMap_correct_of_certificates hsa haa) (bInvMap_correct_of_certificates hsb hab)

/-- The packed A action is the inverse of the original published cycle product. -/
theorem aMap_correct (x : Fin 306936) : aMap x = generatorA x :=
  aMap_correct_of_certificates sourceA_certificate actionsA_certificate x

/-- The opposite packed A action is the inverse of the actual carrier generator. -/
theorem aInvMap_correct (x : Fin 306936) : aInvMap x = generatorA⁻¹ x :=
  aInvMap_correct_of_certificates sourceA_certificate actionsA_certificate x

/-- The packed B action is the inverse of the original published cycle product. -/
theorem bMap_correct (x : Fin 306936) : bMap x = generatorB x :=
  bMap_correct_of_certificates sourceB_certificate actionsB_certificate x

/-- The opposite packed B action is the inverse of the actual carrier generator. -/
theorem bInvMap_correct (x : Fin 306936) : bInvMap x = generatorB⁻¹ x :=
  bInvMap_correct_of_certificates sourceB_certificate actionsB_certificate x

/-- Unconditional signed-letter interpretation for the literal Fi24' generators. -/
theorem letterMap_correct : ∀ c x, letterMap c x = (letterValue c).val x :=
  letterMap_correct_of_generators aMap_correct bMap_correct aInvMap_correct bInvMap_correct

end Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient
