module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22KernelCertificate.Involution
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22KernelCertificate.GeneratorMaps
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22KernelCertificate.GraphInvariance.CycleCheck
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22KernelCertificate.GraphInvariance.BitNetwork

/-!
# The packed map is the exact ATLAS generator A

We use the certified decoding of the original cycle strings. Each cycle sends
the candidate inverse image back to its input, and the candidate fixes the
complement of the cycle support. Disjointness then identifies the inverse
product, including the left-action convention in `Fi22.lean`.
Source: ATLAS F22G1-p3510B0, retained in `AtlasCarriers/source/`.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi22.KernelCertificate
open AtlasCarriers

private def supportMaskA : Nat := 3573446081869082007953492954802312770685283485827712141333729024310699418065560354076615325814394943936188863522096130273690397878245986522475348925373462316944716499858635849270381021562925750858469786732031297042040640303138947324997264185479134875270636554062748882583601829881670197250672191515222968115330963102220339687593074696119193301214719203360913049031352479452331001511648843393273963632005310776045231362489918053913562600277651084930663248599762389366525736894903903086617431711744888477783877577993445027967568525059841635360553550482749472842426151896257561631349937606075773304729917210812639144323673999390701837500911330204466766654615582963636979272572757290553998954535560793463466010875429262579432749165479460334696049367659451497202333510951363734232598898184019650929380125515029586388994947902150117313935043674913770533796881120575133235526845843675872849853004664913269094846835787512502701188496355913045945615474191705390813091632190733408202422570342526115062083102772964722118932464303251826080902783009565432565987810991101

set_option maxRecDepth 100000 in
private theorem supportMaskA_spec : CycleCheck.mask cyclesA.flatten = supportMaskA := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem cycleCheckA :
    (cyclesA.all fun c => c.all fun x => decide (c.formPerm (fastA x) = x)) = true := by
  decide +kernel

private def fixedCheckA (i : Nat) : Bool :=
  supportMaskA.testBit i ||
    decide (fastA ⟨i % 3510, Nat.mod_lt _ (by decide)⟩ =
      ⟨i % 3510, Nat.mod_lt _ (by decide)⟩)

set_option maxRecDepth 100000 in
private theorem fixedCheckA_all : BitNetwork.check fixedCheckA 0 3510 = true := by
  decide +kernel

/-- The packed table agrees with the original inverse ATLAS cycle product. -/
theorem generatorA_apply_eq_fastA (x : Fin 3510) : generatorA x = fastA x := by
  simp only [generatorA, permutationFromCycleBlocks, cyclesA_spec]
  apply CycleCheck.inverse_prod_eq cyclesA fastA cyclesA_nodup
  · simpa only [List.all_eq_true, decide_eq_true_eq] using cycleCheckA
  · intro y hy
    have h := BitNetwork.check_sound fixedCheckA 0 3510 fixedCheckA_all y.val
      (Nat.zero_le _) y.isLt
    rw [supportMaskA_spec] at hy
    simpa only [fixedCheckA, hy, Bool.false_or, Nat.mod_eq_of_lt y.isLt,
      decide_eq_true_eq] using h

end Sporadic.Fischer.Fi22.KernelCertificate
