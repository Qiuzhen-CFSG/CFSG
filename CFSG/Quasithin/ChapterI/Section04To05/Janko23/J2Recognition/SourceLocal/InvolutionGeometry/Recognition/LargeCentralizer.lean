module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.Contracts
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.Reduction
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.QuotientFusion
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SplitNormalizer

/-!
# The large-centralizer branch for J₂ recognition

The local intersection calculation first shows that C_G(t) ≤ N_G(R)
would force order 48. Only then is the order exclusion used to enter
the large branch. Transfer and four-group centralizer recognition produce
an actual marked A₅ subgroup of the literal quotient C_G(t)/⟨t⟩.

The source frame chooses a representative of the second involution class.
The proved quotient fusion and split-extension constructions then give
`UnalignedGeometry`, including the intrinsic component, the placement of z,
and both literal embeddings in the root-core normalizer. Only the exclusion
of order 48 remains an explicit premise, to be discharged by the separate
small-centralizer branch. No ambient order or concrete J₂ identification
is used.

Source: Aschbacher, *Sporadic Groups* (1994), 47.1(1), printed p.260.
-/

@[expose] public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer

variable {G : Type*} [Group G] [Finite G]

/-- Apply the small-intersection calculation before entering the large branch,
then transfer and recognize its literal quotient kernel. -/
theorem LocalFrame.exists_recognized_quotient {D : Seed G} {t : G}
    (F : LocalFrame D t) (ht : OtherInvolution D t)
    (hsmall : Nat.card (involutionCentralizer t) ≠ 48)
    (hquot : ¬ involutionCentralizer t ≤ normalizer (F.R : Set G) →
      Nonempty (QuotientGeometry F)) : Nonempty (RecognizedQuotient F) := by
  obtain ⟨Q⟩ := hquot (F.centralizer_not_le_normalizer hsmall)
  obtain ⟨K, ⟨e⟩⟩ := Q.exists_recognized_kernel ht hsmall
  exact ⟨⟨Q, K, e⟩⟩

theorem RecognizedQuotient.centralizer_card {D : Seed G} {t : G}
    {F : LocalFrame D t} (Q : RecognizedQuotient F) (ht : OtherInvolution D t) :
    Nat.card (involutionCentralizer t) = 240 :=
  Q.kernel.centralizer_card ht.1 Q.equiv

/-- Source 47.1(1), large-centralizer branch: the earlier §46 geometry,
quotient transfer and recognition, and the marked splitting construct the
centralizer and root-core normalizer for a suitable second-class involution.
The separate small-centralizer argument must discharge `hsmall` in the
unconditional source assembly. -/
theorem exists_unalignedGeometry (D : Seed G) (L : LocalCensus D)
    (hsmall : ∀ t : G, OtherInvolution D t → Nat.card (involutionCentralizer t) ≠ 48) :
    ∃ t : G, OtherInvolution D t ∧ Nonempty (UnalignedGeometry D t) := by
  obtain ⟨t, ht, ⟨F⟩⟩ := SourceFrame.exists_localFrame D L
  obtain ⟨Q⟩ := F.exists_recognized_quotient ht (hsmall t ht)
    (fun _ => F.exists_quotientGeometry L ht)
  exact ⟨t, ht, Q.nonempty_unalignedGeometry L ht⟩

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer
