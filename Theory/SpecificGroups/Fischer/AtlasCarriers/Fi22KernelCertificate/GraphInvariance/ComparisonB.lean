module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22KernelCertificate.GraphInvariance.CyclesB
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22KernelCertificate.GeneratorMaps
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22KernelCertificate.GraphInvariance.CycleCheck
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22KernelCertificate.GraphInvariance.BitNetwork

/-!
# The packed map is the exact ATLAS generator B

We use the certified decoding of the original cycle strings. Each cycle sends
the candidate inverse image back to its input, and the candidate fixes the
complement of the cycle support. Disjointness then identifies the inverse
product, including the left-action convention in `Fi22.lean`.
Source: ATLAS F22G1-p3510B0, retained in `AtlasCarriers/source/`.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi22.KernelCertificate
open AtlasCarriers

private def supportMaskB : Nat := 4123678330405087685498374221366984954089317057900104262462784875123790425105688284686404828183633224942349909964891086086676925759584441340507088115762723035704344160664907942351632995309234873230720724730672756917176305067668035542444896101177345052548810184785328926774725935717835798651444434276670015032998880347558303319286200881282911325381616533722737115450145930916961537131913757215277371800137275864121652932255403611649883620607541869985422611380925136858353400304606133084255357430301930613665490583193975084451066213800348446463658847351044167257072998067401824974454641569423021718445571724956556610925411248121271018867103767845126877315661086297321467468234450388231735471475672432407097826847947552577946732477743671085802532103177658853957960953937628759295649081969101068141306491454515657017075167637032474324430969643933568914915807923425951587598028215460799776130796600200956964482108313216473786634870222110938349411949520063457665149056813193039601852026593109271569256781038420076239187040954693149511676801395787300912507360641023

set_option maxRecDepth 100000 in
private theorem supportMaskB_spec : CycleCheck.mask cyclesB.flatten = supportMaskB := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem cycleCheckB :
    (cyclesB.all fun c => c.all fun x => decide (c.formPerm (fastB x) = x)) = true := by
  decide +kernel

private def fixedCheckB (i : Nat) : Bool :=
  supportMaskB.testBit i ||
    decide (fastB ⟨i % 3510, Nat.mod_lt _ (by decide)⟩ =
      ⟨i % 3510, Nat.mod_lt _ (by decide)⟩)

set_option maxRecDepth 100000 in
private theorem fixedCheckB_all : BitNetwork.check fixedCheckB 0 3510 = true := by
  decide +kernel

/-- The packed table agrees with the original inverse ATLAS cycle product. -/
theorem generatorB_apply_eq_fastB (x : Fin 3510) : generatorB x = fastB x := by
  simp only [generatorB, permutationFromCycleBlocks, cyclesB_spec]
  apply CycleCheck.inverse_prod_eq cyclesB fastB cyclesB_nodup
  · simpa only [List.all_eq_true, decide_eq_true_eq] using cycleCheckB
  · intro y hy
    have h := BitNetwork.check_sound fixedCheckB 0 3510 fixedCheckB_all y.val
      (Nat.zero_le _) y.isLt
    rw [supportMaskB_spec] at hy
    simpa only [fixedCheckB, hy, Bool.false_or, Nat.mod_eq_of_lt y.isLt,
      decide_eq_true_eq] using h

end Sporadic.Fischer.Fi22.KernelCertificate
