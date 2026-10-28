module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Models
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.Alignment
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.SmallCentralizer

/-!
# Root-four recognition and selection from the local census

The Sylow-five normalizer argument excludes the order-48 centralizer.
The large-centralizer branch then uses transfer in C_G(t)/⟨t⟩ and A₅
recognition to construct the marked E₄ × A₅ centralizer and compatible
A₄ × A₅ normalizer. Conjugation in C_G(z) aligns this geometry with the
fixed seed vertex, retaining the genuine Sylow condition in the full
component centralizer and all intrinsic subgroup markings.

`selectedGeometry_of_localCensus` discharges both recognition branches;
only the seed and the explicit earlier-source local census remain as inputs.
The argument does not require simplicity of the ambient group.

Source: Aschbacher, *Sporadic Groups* (1994), 47.1(1), pp.259–260.
-/

public section

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition

variable {G : Type*} [Group G] [Finite G]

/-- The source recognition output suffices without an extra premise about `D.X`.
The supplied involution may change under conjugation in C_G(D.z). -/
theorem selectedGeometry_of_unaligned {D : Seed G}
    (h : ∃ t : G, OtherInvolution D t ∧ Nonempty (UnalignedGeometry D t)) :
    Nonempty (SelectedGeometry D) := by
  obtain ⟨t, ht, ⟨S⟩⟩ := h
  exact ⟨S.select ht⟩

/-- Source 47.1(1), with the earlier-source census explicit: exclusion of the
small centralizer, large-centralizer recognition, and conjugation in C_G(z)
construct the full geometry with the prescribed `D.X` as an actual Sylow image.
No further recognition, splitting, or ambient-order premise is needed. -/
theorem selectedGeometry_of_localCensus (D : Seed G) (L : LocalCensus D) :
    Nonempty (SelectedGeometry D) :=
  selectedGeometry_of_unaligned
    (LargeCentralizer.exists_unalignedGeometry D L
      (fun _ ht => SmallCentralizer.not_card_eq_48 L ht))

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition
