module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.Reduction
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.QuotientFusion.Kernel

/-!
# Constructing the marked quotient geometry for source 47.1

From the earlier local frame, the literal quotient C_G(t)/⟨t⟩ has a
marked elementary Sylow eight-group and a fusion-closed four-group.
Every transfer kernel has one involution class and a DihedralGroup 2
involution centralizer. This constructs `QuotientGeometry`, discharging
the geometry premise of the existing transfer and A₄/A₅ reduction.

Only the involution order, local census and frame are needed for this
step. The source's exclusion of the centralizer of order 48 is retained
as an explicit premise of the recognition consumer.

Source: Aschbacher, *Sporadic Groups* (1994), 47.1(1), printed p.260.
The checked BSW reduction replaces the source's FGT Exercise 16.6.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer
variable {G : Type*} [Group G] [Finite G] {D : Seed G} {t : G}

/-- The marked quotient geometry follows from the earlier local frame.
No large-centralizer inequality or simplicity premise is needed here. -/
def LocalFrame.quotientGeometry (F : LocalFrame D t) (L : LocalCensus D)
    (ht : orderOf t = 2) : QuotientGeometry F where
  transfer := F.quotientTransfer L ht
  sylow_eq := F.quotientSylow_eq
  closed_eq := F.quotientClosed_eq
  kernel_local := F.quotient_kernel_local L ht

/-- Conditional constructor for the literal quotient used in source 47.1(1). -/
theorem LocalFrame.exists_quotientGeometry (F : LocalFrame D t) (L : LocalCensus D)
    (ht : OtherInvolution D t) : Nonempty (QuotientGeometry F) :=
  ⟨F.quotientGeometry L ht.1⟩

/-- Consumer application: the newly constructed fusion data discharges the
quotient-geometry premise of the existing transfer and recognition reduction. -/
theorem LocalFrame.exists_recognizedQuotient (F : LocalFrame D t) (L : LocalCensus D)
    (ht : OtherInvolution D t) (hsmall : Nat.card (involutionCentralizer t) ≠ 48) :
    Nonempty (RecognizedQuotient F) := by
  let Q := F.quotientGeometry L ht.1
  obtain ⟨K, ⟨e⟩⟩ := Q.exists_recognized_kernel ht hsmall
  exact ⟨⟨Q, K, e⟩⟩
end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer
