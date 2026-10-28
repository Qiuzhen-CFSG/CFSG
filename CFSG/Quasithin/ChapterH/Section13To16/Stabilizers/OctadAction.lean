module

public import Theory.Mathieu.M24.ChapterHStabilizers.OctadAction
public import CFSG.Quasithin.ChapterH.Section13To16.Defs

/-!+# H.14.1(4): the intrinsic octad kernel and its natural action

The chapter's literal mapped two-core is the additive binary four-space.
Conjugation is its natural action under the actual quotient identification
with PSL4(2). The action is surjective and its kernel is precisely the
intrinsic two-core. All these statements hold for every native octad, with
no additional coordinate, action or model-comparison premise.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.14.1(4),
printed pp.396–397.
-/

@[expose] public section

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M24ChapterHStabilizers
open scoped MatrixGroups Pointwise

namespace CFSG.Quasithin.ChapterH.Section13To16
noncomputable section

/-- The source's mapped intrinsic octad kernel is elementary abelian. -/
theorem octadKernel_elementary (O : Octad) : IsElementaryAbelian 2 (octadKernel O) :=
  OctadAction.ambientCore_elementary O

/-- The source's mapped intrinsic octad kernel has order sixteen. -/
theorem octadKernel_card (O : Octad) : Nat.card (octadKernel O) = 16 :=
  OctadAction.ambientCore_card O

/-- Coordinates in the literal chapter kernel, at any native octad. -/
def octadKernel_naturalEquiv (O : Octad) :
    Multiplicative (Fin 4 → ZMod 2) ≃* octadKernel O :=
  (OctadAction.ambientCoordinates O).symm

/-- The quotient uses the intrinsic core of the actual stabilizer. -/
def octadStabilizer_naturalQuotientEquiv (O : Octad) :
    (octadStabilizer O ⧸ pCore 2 (octadStabilizer O)) ≃* PSL(4, ZMod 2) :=
  OctadAction.quotientEquiv O

/-- Conjugation in the native stabilizer, expressed on the binary four-space. -/
def octadStabilizer_naturalAction (O : Octad) :
    octadStabilizer O →* ((Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 → ZMod 2)) :=
  OctadAction.linearAction O

theorem octadStabilizer_naturalAction_surjective (O : Octad) :
    Function.Surjective (octadStabilizer_naturalAction O) :=
  OctadAction.linearAction_surjective O

theorem octadStabilizer_naturalAction_ker (O : Octad) :
    (octadStabilizer_naturalAction O).ker = pCore 2 (octadStabilizer O) :=
  OctadAction.linearAction_ker O

/-- The quotient marking induces precisely the conjugation action in these coordinates. -/
theorem octadStabilizer_naturalAction_quotient (O : Octad) (g : octadStabilizer O) :
    OctadAction.naturalAction
      (octadStabilizer_naturalQuotientEquiv O (QuotientGroup.mk g)) =
        octadStabilizer_naturalAction O g :=
  OctadAction.naturalAction_quotientEquiv O g

/-- H.14.1(4): the literal chapter kernel is the natural module for its stabilizer quotient. -/
theorem octadKernel_natural_conjugation (O : Octad) (g : octadStabilizer O)
    (v : Fin 4 → ZMod 2) :
    g.val * (octadKernel_naturalEquiv O (Multiplicative.ofAdd v)).val * g.val⁻¹ =
      (octadKernel_naturalEquiv O (Multiplicative.ofAdd
        (OctadAction.naturalAction
          (octadStabilizer_naturalQuotientEquiv O (QuotientGroup.mk g)) v))).val :=
  OctadAction.ambientCoordinates_conjugation O g v

/-- The actual M24 conjugator transports the chapter's mapped cores. -/
def octadKernel_transport (O P : Octad) (g : M24) (hg : g • O.val = P.val) :
    octadKernel O ≃* octadKernel P := OctadAction.ambientTransport O P g hg

theorem octadKernel_transport_apply (O P : Octad) (g : M24) (hg : g • O.val = P.val)
    (a : octadKernel O) : (octadKernel_transport O P g hg a).val = g * a.val * g⁻¹ :=
  OctadAction.ambientTransport_apply O P g hg a

end
end CFSG.Quasithin.ChapterH.Section13To16
