module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.TitsCubicDisplacement.ElementaryGeometry.FiveCommutators
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.TitsCubicDisplacement.ElementaryGeometry.Centralizers
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.TitsCubicDisplacement.ElementaryGeometry.Rank
public import Theory.SpecificGroups.Tits.InvolutionRootGeometry.Reduction

/-!
# Assembly of the finite geometry for the Tits displacement estimate

Full binary involution coverage puts each nonidentity Parrott involution in
one of the two marked root classes. The explicit five-element commutators
are already certified for both representatives. Relative-normality bounds
transport from those representatives without changing the forbidden class.

The certified Sylow coloring supplies rank at most five, and the certified
short-root conjugators bound every elementary subgroup avoiding the literal
five-inverter class by sixteen. Thus `localGeometry_of_coverage` constructs
all three local clauses with binary involution coverage as its only premise.
Its independent producer is `qt-16-tits-binary-involution-coverage`; the parent
displacement task retains that discharge and the five-weight estimates.
`ElementaryGeometry.InternalApplication` supplies the actual representation
consumer. Sources: GM04 Table 13 and Lemmas 2.3, 8.8;
Aschbacher–Smith, `refs/quasithin.pdf`, printed p.457.
-/

public section
namespace CFSG.Quasithin.ChapterK.Exceptional.TitsCubicDisplacement.ElementaryGeometry
open Subgroup Tits Tits.InvolutionRootGeometry

/-- Binary coverage supplies the two literal Parrott root classes. -/
theorem root_classes_of_coverage (hcover : BinaryInvolutionCoverage)
    (t : ParrottGroup) (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    IsConj (parrottGenerator .s1) t ∨ IsConj (parrottGenerator .s4) t := by
  have hg2 : (derivedEquiv t : ReeF4.Model 0) ^ 2 = 1 := by
    change embedding t ^ 2 = 1
    rw [← map_pow, ht2, map_one]
  have hgn : (derivedEquiv t : ReeF4.Model 0) ≠ 1 := by
    intro he
    exact ht (embedding_injective (he.trans (map_one embedding).symm))
  obtain ⟨x, hx, hc⟩ := hcover (derivedEquiv t) hg2 hgn
  have he : x = derivedEquiv t := Subtype.ext hx
  rw [he] at hc
  exact hc.imp ((isLongRoot_iff t).mp) ((isShortRoot_iff t).mp)

/-- Only the two literal root centralizers need separate finite certificates. -/
theorem normal_elementary_of_root_bounds (hcover : BinaryInvolutionCoverage)
    (hlong : NormalElementaryBound (parrottGenerator .s1))
    (hshort : NormalElementaryBound (parrottGenerator .s4))
    (t : ParrottGroup) (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    NormalElementaryBound t := by
  rcases root_classes_of_coverage hcover t ht ht2 with h | h
  · exact hlong.conjugate h
  · exact hshort.conjugate h

/-- The commutator clause needs only the given binary involution coverage. -/
theorem five_commutator_of_coverage (hcover : BinaryInvolutionCoverage)
    (t : ParrottGroup) (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    ∃ x k : ParrottGroup, k ∈ fiveKernel ∧ k ≠ 1 ∧
      IsConj k (t * x * t⁻¹ * x⁻¹) := by
  rcases root_classes_of_coverage hcover t ht ht2 with h | h
  · exact commutator_conjugate h long_five_commutator
  · exact commutator_conjugate h short_five_commutator

/-- Assembly with the finite calculations stated explicitly, retained for
clients that supply their own bounds. -/
theorem localGeometry_of_rank_and_root_bounds (hcover : BinaryInvolutionCoverage)
    (hrank : primeRank 2 ParrottGroup ≤ 5)
    (hlong : NormalElementaryBound (parrottGenerator .s1))
    (hshort : NormalElementaryBound (parrottGenerator .s4)) : LocalGeometry where
  elementary_rank := hrank
  five_commutator := five_commutator_of_coverage hcover
  normal_elementary := normal_elementary_of_root_bounds hcover hlong hshort

/-- The exact finite local geometry, with only binary involution coverage
remaining as an input. Rank, commutators and both centralizer bounds are proved. -/
theorem localGeometry_of_coverage (hcover : BinaryInvolutionCoverage) : LocalGeometry :=
  localGeometry_of_rank_and_root_bounds hcover parrott_two_rank_le_five
    long_normal_elementary_bound short_normal_elementary_bound

end CFSG.Quasithin.ChapterK.Exceptional.TitsCubicDisplacement.ElementaryGeometry
