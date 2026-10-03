module

public import Stellmacher.SectionEight.EightTwoBackwardNativeModuleEnvelope
public import Stellmacher.SectionEight.EightTwoBackwardCoreOmegaNeighbor

/-!
# The native-module upper bound in Stellmacher (8.2)

Assume that the first-step vertex center is noncentral, the critical path
has length greater than one, and the first-edge core intersection is normal
in the initial stabilizer. For every supplied Sylow subgroup of
`L = Ea ⊔ Qfirst` with ambient image exactly `Qfirst`, its native Section Two
module maps into the neighbor module `Vfirst`.

The native-module envelope identifies the mapped module with the join of
`Za` and the omega-center of `Qfirst`. The first subgroup lies in `Vfirst`
by the critical-path containment. The neighboring-core omega theorem puts
the second there using the dihedral core quotient and Thompson
noncontainment. Applying the envelope's upper-bound equivalence completes
the comparison without changing the supplied Sylow or identifying `L`
with the initial stabilizer.

This is the upper comparison needed to identify the actual native-module
Hall orbit in the first containment case of Stellmacher (8.2), journal
pp.37–38, `refs/latex/stellmacher-n-group.tex`. The Hall-orbit assembly is
separate; neither that equality nor the final contradiction is assumed.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven
universe u

public theorem eight_two_backward_native_module_le_neighbor
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hlen : 1 < ctx.criticalPath.length)
    (hnormal : NormalIn
      (QAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
      (GAt ctx.Γ ctx.criticalPath.a))
    (T : Sylow 2 ↥(EAt ctx.Γ ctx.criticalPath.a ⊔ QAt ctx.Γ ctx.criticalPath.firstStep))
    (hT : (T : Subgroup ↥(EAt ctx.Γ ctx.criticalPath.a ⊔
      QAt ctx.Γ ctx.criticalPath.firstStep)).map
        (EAt ctx.Γ ctx.criticalPath.a ⊔ QAt ctx.Γ ctx.criticalPath.firstStep).subtype =
          QAt ctx.Γ ctx.criticalPath.firstStep) :
    (SectionTwo.vSubgroup T).map
      (EAt ctx.Γ ctx.criticalPath.a ⊔ QAt ctx.Γ ctx.criticalPath.firstStep).subtype ≤
        VAt ctx.Γ ctx.criticalPath.firstStep := by
  exact (eight_two_backward_native_le_neighbor_iff_omega_le ctx hnormal T hT).mpr
    (eight_two_backward_core_omega_le_neighbor ctx hcenter hlen hnormal)

end Stellmacher.SectionEight
