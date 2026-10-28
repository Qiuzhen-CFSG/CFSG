module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.WordChecks.Reduction
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.WordChecks.Numerical

/-!
# The checked source-label candidate actions

The addition chains 1,2,3,5,10,15,30 and 1,2,3,6 turn the small composition
certificates into the exact powers used by the two candidates. The final
checked conjugation retains the order u s w and its reverse inverse order.
Source: the literal `WordSetup` formulas; the numerical witnesses and their
kernel certificates are in `AuxiliaryData` and `Numerical`.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient.WordChecks

private theorem a2_iter (i : Fin 31671) : a2Map i = iterateSource a1Map 2 i :=
  a2Map_spec i

private theorem a3_iter (i : Fin 31671) : a3Map i = iterateSource a1Map 3 i := by
  rw [a3Map_spec, a2_iter]
  rfl

private theorem a5_iter (i : Fin 31671) : a5Map i = iterateSource a1Map 5 i := by
  rw [a5Map_spec, a3_iter, a2_iter, ← iterateSource_add]

private theorem a10_iter (i : Fin 31671) : a10Map i = iterateSource a1Map 10 i := by
  rw [a10Map_spec, a5_iter, a5_iter, ← iterateSource_add]

private theorem a15_iter (i : Fin 31671) : a15Map i = iterateSource a1Map 15 i := by
  rw [a15Map_spec, a10_iter, a5_iter, ← iterateSource_add]

/-- The checked addition chain gives the exact thirtieth power. -/
theorem smallA_eq_sourceA (i : Fin 31671) : smallA i = sourceA i := by
  have h : (fun j => wInvMap (rMap (vInvMap j))) = a1Map :=
    (funext a1Map_spec).symm
  rw [smallA, h, sourceA_spec, a15_iter, a15_iter, ← iterateSource_add]

private theorem b2_iter (i : Fin 31671) : b2Map i = iterateSource b1Map 2 i :=
  b2Map_spec i

private theorem b3_iter (i : Fin 31671) : b3Map i = iterateSource b1Map 3 i := by
  rw [b3Map_spec, b2_iter]
  rfl

private theorem b6_iter (i : Fin 31671) : b6Map i = iterateSource b1Map 6 i := by
  rw [b6Map_spec, b3_iter, b3_iter, ← iterateSource_add]

/-- The checked sixth power and conjugation give the exact second source map. -/
theorem smallB_eq_sourceB (i : Fin 31671) : smallB i = sourceB i := by
  have h : (fun j => uInvMap (vMap (vMap j))) = b1Map :=
    (funext b1Map_spec).symm
  rw [smallB, h, sourceB_spec, b6_iter]

end Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient.WordChecks
