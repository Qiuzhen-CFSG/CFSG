module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.BinaryInspection.Cases
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.BinaryInspection.Kernel
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.BinaryInspection.MiddleEight
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.BinaryInspection.LinearInspection
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.BinaryInspection.ExceptionalInspection.G2
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.BinaryInspection.ExceptionalInspection.Triality
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.BinaryInspection.ExceptionalInspection.Tits
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.BinaryInspection.SixInspection

/-!
# The binary inspection in 15.3.43

The complete source model list reduces to binary linear, exceptional, and
A₆ branches, using the actual Sp₄(2)′ comparison and excluding the triple
cover before recovering the original A₆ component.

The linear inspection derives the maximal invariant parabolic from the
retained configuration. It excludes PSL₅(2) and constructs both markings for
the PSL₄(2) extension: the component intersection is the even pair stabilizer,
while the full local image is the S₈ pair stabilizer. Its intrinsic two-radical
obstructs the normal four-group. The exceptional inspections use the source
involution to place actual centralizers or a Levi subgroup in the local group,
excluding G₂(2)′, triality and the Tits group. Finally, the A₆ inspection
constructs I/C_I(L) ≃ S₆ and Y₊ ≃ A₄ with their actual kernels, contradicting
the retained exclusion of A₄.

Thus `not_binary` closes the n = 1 branch from precisely the reduced
configuration, source involution and source model. Constructing that reduced
configuration and handling larger fields remain with the enclosing theorem.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), the n = 1
paragraph of 15.3.43, printed p.1140.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.BinaryInspection

variable {G : Type*} [Group G] [Finite G]
variable {Yplus S M I L V₁ V₂ : Subgroup G}

/-- Every remaining binary model is excluded by its actual local inspection. -/
theorem not_remaining_model (c : ReducedConfiguration Yplus S M I L V₁ V₂)
    {z : G} (hz : SourceInvolution S M z) (hm : RemainingModel L z) : False := by
  cases hm with
  | linear hs d hd iso hi =>
    exact LinearInspection.not_linear c hz hs hd iso hi
  | exceptional hs hm hi =>
    cases hm with
    | g2Derived iso => exact ExceptionalInspection.not_g2_derived c hz hs hi iso
    | triality iso => exact ExceptionalInspection.not_triality c hz hs hi iso
    | tits iso => exact ExceptionalInspection.not_tits c hz hs hi iso
  | alternatingSix iso ha =>
    exact c.not_alternating_four (SixInspection.identifications c hz iso ha).2

/-- The complete binary case of the characteristic-two model exclusion in
15.3.43, with no additional local classification or recognition premise. -/
theorem not_binary (c : ReducedConfiguration Yplus S M I L V₁ V₂)
    {z : G} (hz : SourceInvolution S M z) (hm : Model L z 1) : False :=
  not_remaining_model c hz (remaining_model c hm)

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.BinaryInspection
