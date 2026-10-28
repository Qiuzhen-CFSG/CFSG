module
public import Theory.SpecificGroups.PSL3Two.ProperSubgroups
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel
public import Theory.GroupTheory.SolvableSylowOvergroups

/-!
# Solvable proper Sylow overgroups in binary linear dimension three

Entrywise field transport identifies SL₃ over any two-element field with
the actual SL₃(ZMod 2). Its proper subgroups are solvable. The canonical
center quotient identifies SL₃(2) with PSL₃(2), giving the projective
version with the same field marking.

These intrinsic results remove the binary linear endpoint in the proper
containing-component argument of Aschbacher–Smith 5.2.2, printed p.648.
Field transport and the underlying order-168 model retain the attribution
and license of the imported ATLAS ports; see LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Matrix.PSL3Two
variable {F : Type*} [Field F] [Finite F]

/-- Proper Sylow overgroups of SL₃ over any two-element field are solvable. -/
theorem solvableSylowOvergroups_specialLinear_of_card_two (hF : Nat.card F = 2) :
    SolvableSylowOvergroups (SpecialLinearGroup (Fin 3) F) := by
  let := Fintype.ofFinite F
  let a : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
  exact SolvableSylowOvergroups.of_equiv (Atlas.fieldEquivSL 3 a)
    (fun _ P _ hP => isSolvable_subgroup_SL_of_ne_top P hP)

/-- The projective binary model has the same property through its actual
field map and the canonical SL₃(2) to PSL₃(2) isomorphism. -/
theorem solvableSylowOvergroups_projective_of_card_two (hF : Nat.card F = 2) :
    SolvableSylowOvergroups (ProjectiveSpecialLinearGroup (Fin 3) F) := by
  let := Fintype.ofFinite F
  let a : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
  exact SolvableSylowOvergroups.of_equiv ((Atlas.fieldEquivPSL 3 a).trans equiv.symm)
    (fun _ P _ hP => isSolvable_subgroup_SL_of_ne_top P hP)
end Matrix.PSL3Two
