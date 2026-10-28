module

public import Theory.Representation.PSL3Two.ParabolicCyclic.ChiefCounts.DualCore.Dual
public import Theory.Representation.PSL3Two.ParabolicCyclic.ChiefCounts.DualCore.Extension
public import Theory.Representation.PSL3Two.FanoCoreStructure

/-!
# Chief counts on the dual natural module and the Fano point core

The dual flag is re-exported from `Dual`. For the actual six-dimensional
point core, the weighted-sum kernel is dual natural and the literal quotient
is natural. Restrict both equivariant identifications to the embedded
line-parabolic two-residual and lift their complete flags through this exact
sequence. The resulting core flag has two noncentral sections; no direct-sum
identification of the nonsplit core is used.

Source: Aschbacher–Smith H.5.3(1–2), H.5.2, and 14.7.22(2), with the
line-parabolic marking in H.6.5.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Representation
namespace BinaryLinearThree.ParabolicCyclic.ChiefCounts
open FanoCoreStructure
/-- The literal Fano point core has two noncentral chief factors under the
embedded two-residual of the line parabolic. The flags of its dual-natural
kernel and natural quotient are lifted through the nonsplit exact sequence. -/
theorem core_count : HasCount (U₂.comp actor.subtype) 2 := by
  let K : Subrepresentation (U₂.comp actor.subtype) := {
    toSubmodule := pointKernel.toSubmodule
    apply_mem_toSubmodule g _ hv := pointKernel.apply_mem_toSubmodule g.val hv }
  have hK : HasCount K.toRepresentation 1 :=
    dual_count.mapEquiv (restrictEquiv pointKernelEquiv actor.subtype)
  have hQ : HasCount K.quotientRepresentation 1 :=
    natural_count.mapEquiv (restrictEquiv pointQuotientEquiv.symm actor.subtype)
  exact HasCount.of_subrepresentation K hK hQ
end BinaryLinearThree.ParabolicCyclic.ChiefCounts
