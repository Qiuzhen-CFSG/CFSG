module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalCover.SourceBorel.Reduction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalCover.SourceBorel.BorelConstruction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalCover.SourceBorel.CyclicPlanes

/-!
# Constructing the compatible Borel and root-plane data

The Borel construction supplies N_L(S ∩ L), its local placement and normalizer,
and the order-three quotient of Y_L = O²(Y₊ ∩ L). Projective rigidity identifies
C_S(Y_L) with C_S(L), so Y_L acts nontrivially on V. The cyclic-plane theorem
then chooses the two original planes compatibly and supplies an actual element
of T interchanging them. The moving plane lies in S ∩ L, and its nontrivial
Borel-invariant projective image contains an inner conjugate of the root.

`orientedBorelData_of_calculations` constructs both intermediate outputs;
neither is an assumption. The earlier source conclusions are uniform over
eligible outside overgroups. The precise intrinsic projective, central-cover,
rigidity and root calculations remain explicit inputs, as permitted by this
conditional construction. The original quotient marking and diagonal actor
are retained throughout. The deductions n = 2 and Y₊ = Y, and the completion
of source 15.3.38, belong to the consuming local-cover assembly.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.2--12, 15.3.25, 15.3.33--37 and the proof of 15.3.38,
printed pp.1121--1125 and 1134--1136.
-/

public section

open Subgroup Theory.GroupTheory
open scoped Pointwise

namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover.SourceBorel

variable {G : Type*} [Group G] [Finite G]
variable {d : CharacteristicTwo.LocalData G} {I L : Subgroup G}

/-- Construct the oriented Borel output for the given marking and diagonal
actor. The positive-three-order input is the consequence of earlier 15.3.34
for ordinary components, uniformly over the outside family. All local Borel
and plane conclusions are derived; only the intrinsic model calculations
remain conditional inputs. -/
theorem orientedBorelData_of_calculations (h : Setup d I L) (e : Earlier d)
    (h34 : ∀ J ∈ d.Hplus, ∀ K : Subgroup J, IsComponent J K → 3 ∣ Nat.card K)
    {n : ℕ} (hn : 0 < n) (heven : Even n) (c : ProjectiveMarking L (2 ^ n))
    {y : G} (hy : y ∈ d.Yplus) (hdiag : c.Diagonal y)
    (hproduct : (d.Yplus : Set G) =
      (componentPart d.Yplus L : Set G) * (zpowers y : Set G))
    (m : ProjectiveBorelCalculations c) (k : CentralCoverBorelCalculations c)
    (r : MatrixTests c) :
    Nonempty (OrientedBorelData d.M d.Yplus d.S L d.V₁ d.V₂ c) := by
  obtain ⟨b⟩ := borelStep_of_calculations h e (h34 I h.outside)
    hn heven c hy hdiag hproduct m k
  exact orientedBorelData_of_borel_and_plane_theorem h e r b
    (cyclicPlaneChoice_of_card_quotient_three d)

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover.SourceBorel
