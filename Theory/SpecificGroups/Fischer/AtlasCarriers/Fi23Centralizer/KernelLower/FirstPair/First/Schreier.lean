module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelLower.FirstPair.First.Initial
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelLower.FirstPair.First.Schreier.Cancellation

/-!
# Assembly of the remaining Fi23 transitions at letter 40

Cancellation and involution reversal reduce the positive equations to the
explicit Residual family. This module connects that family to the original
Step statements and to the actual stabilizer containment. The residual
families remain explicit until their independent equation certificates are
available; no group order or GAP stabilizer assertion is used.

Source: retained ATLAS F23G1-p31671B0; GLS3 Table 5.3u and the Fischer paragraph
near line 1042 of refs/KGroup/GLS3/Chapter5(sec3-).tex.
-/

public section
namespace Sporadic.Fischer.Fi23.CentralizerSection

namespace KernelLowerFirstPair.First

/-- Recover every original positive equation from the residual families. -/
theorem steps_of_residual (h : ∀ a : Fin 7, Schreier.Residual a) : ∀ a : Fin 7, Step a :=
  fun a => Schreier.step_of_residual a (h a)

end KernelLowerFirstPair.First

/-- Literal first suffix consumer; the residual equations remain outstanding. -/
theorem packed_first_suffix_le_of_residual
    (h : ∀ a : Fin 7, KernelLowerFirstPair.First.Schreier.Residual a)
    (p : Equiv.Perm (Fin 31671)) (hp : p ∈ KernelUpperThird.packedSubgroup)
    (h40 : p 40 = 40) : p ∈ KernelLowerFirstPair.afterOne :=
  (KernelLowerFirstPair.First.reduction
    (KernelLowerFirstPair.First.steps_of_residual h)).mem_next hp h40

end Sporadic.Fischer.Fi23.CentralizerSection
