module

public import Theory.SpecificGroups.Triality.OddFundamentalCentralizer.Centralizer.Lifts
public import Theory.SpecificGroups.Triality.OddFundamentalCentralizer.Centralizer.ElementaryIndex.FixedArms

/-!
# The split subgroups used in the odd triality index calculation

The centralizer here is taken in the genuine split D4 matrix group and uses the
full cubic-field central SL₂. The complementary split subgroup is the image of
all three arm factors under the exact inverse conjugation from `Centralizer/Lifts`.
Its graph-field fixed part is proved to be the marked complementary SL₂.

These definitions give the untwisted geometric calculation a boundary independent
of the elementary group and the central quotient. No split-centralizer exhaustion
or index assertion is assumed or proved here.

Sources: GLS3 §§2.4, 2.6 (`refs/KGroup/GLS3/chapter2.tex`);
Aschbacher–Smith A.2.17, printed p.39.
-/

@[expose] public section
noncomputable section
open Matrix
open scoped MatrixGroups
namespace Triality.Standard.OddFundamentalCentralizer.ElementaryIndex
open Parabolics

variable {P : Parameters} (D : PinnedRankOneMaps P) (C : ArmRootCommutation P)

/-- The centralizer of the full split central rank-one subgroup. -/
def splitCentralizer : Subgroup (SplitGroup P) :=
  Subgroup.centralizer ((D.hom 1).range : Set (SplitGroup P))

/-- Inverse conjugation of the full three-arm product, ordered 0, 2, 3. -/
def splitComplementProduct :
    (SL(2, ExtensionField P) × SL(2, ExtensionField P)) × SL(2, ExtensionField P) →*
      SplitGroup P :=
  (MulAut.conj (splitHighestWeyl D C)⁻¹).toMonoidHom.comp (D.armsProduct C)

/-- The actual complementary split subsystem inside the Geck matrix group. -/
def splitComplementSubgroup : Subgroup (SplitGroup P) :=
  (splitComplementProduct D C).range

/-- The prescribed diagonal gives exactly the marked complementary map. -/
theorem splitComplementProduct_diagonal (a : SL(2, ExtensionField P)) :
    splitComplementProduct D C (PinnedRankOneMaps.armsDiagonal P a) =
      splitComplementHom D C a := rfl

/-- Fixed points of the split subsystem are exactly the complementary SL₂ image. -/
theorem range_splitComplementHom :
    (splitComplementHom D C).range = splitComplementSubgroup D C ⊓ fixedSubgroup P := by
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    exact ⟨⟨PinnedRankOneMaps.armsDiagonal P a, rfl⟩, (complementLift D C a).val.property⟩
  · rintro x ⟨⟨s, rfl⟩, hx⟩
    have hw : splitHighestWeyl D C ∈ fixedSubgroup P := (highestLift D C).val.property
    have hy : D.armsProduct C s ∈ fixedSubgroup P := by
      have h := (fixedSubgroup P).mul_mem
        ((fixedSubgroup P).mul_mem hw hx) ((fixedSubgroup P).inv_mem hw)
      change splitHighestWeyl D C *
        ((splitHighestWeyl D C)⁻¹ * D.armsProduct C s * splitHighestWeyl D C) *
        (splitHighestWeyl D C)⁻¹ ∈ fixedSubgroup P at h
      simpa only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left] using h
    have hr : D.armsProduct C s ∈ (D.armsFixedEmbedding C).range :=
      (range_armsFixedEmbedding D C).ge
        ⟨(D.range_armsProduct C).le ⟨s, rfl⟩, hy⟩
    obtain ⟨a, ha⟩ := hr
    exact ⟨a, congrArg (MulAut.conj (splitHighestWeyl D C)⁻¹) ha⟩

end Triality.Standard.OddFundamentalCentralizer.ElementaryIndex
