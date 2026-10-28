module

public import Theory.Mathieu.M24.ChapterHStabilizers.TrioAction.AllTrios
public import CFSG.Quasithin.ChapterH.Section13To16.Defs

/-!
# H.14.1(3): the intrinsic trio kernel and its tensor action

The chapter's literal mapped two-core is elementary abelian of order 64.
The native tensor equivalence identifies it with the natural three-space for
PSL3(2) tensored with the natural two-space for S3, and intertwines actual
stabilizer conjugation with the quotient by the intrinsic core. Both the
existing standard quotient marking and geometric transport to every trio are
retained. All coordinate, kernel and transport premises are discharged by the
native Theory construction.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.14.1(3),
printed pp.396–397.
-/

@[expose] public section

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open MathieuCode.TrioCalculation
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterH.Section13To16
noncomputable section
open Sporadic.Mathieu.M24ChapterHStabilizers

/-- The source's mapped intrinsic trio kernel is elementary abelian. -/
theorem trioKernel_elementary (T : Trio) : IsElementaryAbelian 2 (trioKernel T) :=
  TrioAction.coreAt_elementary T

/-- The source's mapped intrinsic trio kernel has order 64. -/
theorem trioKernel_card (T : Trio) : Nat.card (trioKernel T) = 64 := TrioAction.coreAt_card T

/-- Tensor identification at the standard marking, compatible with the existing quotient. -/
def standardTrioKernel_tensorEquiv :
    Multiplicative NaturalTensor ≃* trioKernel standardTrio := TrioAction.ambientTensorEquiv

theorem standardTrioKernel_tensor_conjugation
    (g : trioStabilizer standardTrio) (z : NaturalTensor) :
    g.val * (standardTrioKernel_tensorEquiv (Multiplicative.ofAdd z)).val * g.val⁻¹ =
      (standardTrioKernel_tensorEquiv (Multiplicative.ofAdd
        (TrioAction.sourceTensorRepresentation
          (standardSourceQuotientEquiv (QuotientGroup.mk g)) z))).val :=
  TrioAction.ambientTensorEquiv_conjugation g z

/-- The tensor group is the literal kernel at every geometric trio. -/
def trioKernel_tensorEquiv (T : Trio) : Multiplicative NaturalTensor ≃* trioKernel T :=
  TrioAction.tensorEquivAt T

/-- Quotient identification transported by the same native geometric conjugation. -/
def trioStabilizer_tensorQuotientEquiv (T : Trio) :
    (trioStabilizer T ⧸ pCore 2 (trioStabilizer T)) ≃*
      (PSL(3, ZMod 2) × Equiv.Perm (Fin 3)) := TrioAction.sourceQuotientEquivAt T

/-- H.14.1(3) on the chapter's actual `trioKernel`, with both natural actions. -/
theorem trioKernel_tensor_conjugation (T : Trio) (g : trioStabilizer T) (z : NaturalTensor) :
    g.val * (trioKernel_tensorEquiv T (Multiplicative.ofAdd z)).val * g.val⁻¹ =
      (trioKernel_tensorEquiv T (Multiplicative.ofAdd
        (TrioAction.sourceTensorRepresentation
          (trioStabilizer_tensorQuotientEquiv T (QuotientGroup.mk g)) z))).val :=
  TrioAction.tensorEquivAt_conjugation T g z

end
end CFSG.Quasithin.ChapterH.Section13To16
