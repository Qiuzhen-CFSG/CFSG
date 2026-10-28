module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Coordinates
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Enumeration.Transport
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Enumeration.Centralizers
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Enumeration.Lifts

/-!
# The alternating-five elementary-family calculation

Given the actual permutation coordinates, the full maximum-order elementary
family of `S` consists of `Q`, its opposite, and the two transposition lifts.
The fixed-centralizer profile in `Q = UD` bounds every elementary subgroup's
order by `|Q|`. The opposite is a conjugate of `Q`, and each transposition
lift has that same order. The fixed-space uniqueness argument exhausts the
family, excluding the double-transposition line by its larger fixed index.

The assembly below proves each input to this intrinsic enumeration and then
transports the entire family and its action images from `S` to `G`. Only
construction of the explicitly supplied `ActionCoordinates` remains the
responsibility of the caller, as specified by `EnumerationInput`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.3.2 and
B.2.21, and the proof of C.5.6, printed pp.157–158.
-/

public section
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily
open Enumeration
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Under the published source hypotheses and actual permutation coordinates,
the four specified subgroups exhaust the maximum-order elementary family. -/
theorem enumerationInput (K : GroupClass.{u}) : EnumerationInput (G := G) K := by
  intro A H R L h hb _hL x hx _hnc hp hf c
  obtain ⟨hQ, hW⟩ := intrinsic_elementary h hb hp hf
  obtain ⟨B₀, B₁, hfamily, h₀, h₁⟩ :=
    exists_maxFamily_eq_four (restrictedAction c) (coreIn R L) (oppositeIn R L x)
      hQ hW (restrictedAction_ker c hb) (restrictedAction_range c)
      (oppositeIn_image c hb hp) (oppositeIn_card h hb hx hp c)
      (fixedProfile h hb hp hf c)
  exact family_of_intrinsic_enumeration hb hp c hfamily h₀ h₁

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily
end
