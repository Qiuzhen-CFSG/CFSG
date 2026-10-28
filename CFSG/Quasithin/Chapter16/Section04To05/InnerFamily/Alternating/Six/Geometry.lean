module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Alternating.Six.Geometry.Choices
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Alternating.Six.Geometry.ActionImage
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Alternating.Six.Geometry.MarkedPlacement
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Alternating.Six.Geometry.OvergroupDichotomy
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Alternating.Six.Geometry.LocalStabilizer

/-!
# Local geometry for the marked A₆ branch

The compatible conjugator retains the original component and proves z ∼ r.
Conjugation inside LE places the model's elementary sixteen-group A in the
original Sylow subgroup T. Correcting a conjugator at each marked point gives
an actual conjugate of LE containing all four marks, with its index-two
subgroup conjugate to L⟨z⟩. Under the contrary empty-Δ₀ assumption, these
overgroups exclude the products of two or three distinct marks from zᴳ.

The genuine normalizer image on L is either the natural S₆ or all of Aut(A₆).
In the natural case, Sylow orders and the centralizer kernel give LT = LE.
Independently of either fusion branch, the normalizer point stabilizer acts
faithfully on the three noncentral marks, and even permutations of coordinate
pairs realize S₃. Its order is therefore six.

`exists_local_geometry` assembles these constructions for the A₆ branch,
retaining T, z, r and L. It uses only the earlier source inputs in
`IntersectionSetup` and `OrderTwoOutsideDeltaZero`, the supplied actual product
model and component isomorphism, and the contrary empty-Δ₀ hypothesis. No
placement, marked containment, product exclusion, ambient dichotomy, stabilizer
order or global fusion conclusion is assumed. The total-product fusion and
normalizer transitivity needed to finish 16.4.9(2) belong to the two fusion
branches and the parent assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 16.4.9(2), printed p.1192 (PDF p.1209).
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter16.Intersections.Six
variable {G : Type*} [Group G] {L : Subgroup G} {z r : G}

/-- The full-automorphism condition uses the actual action and is independent
of which isomorphism from L to A₆ supplies its coordinates. -/
theorem fullAutomorphismCase_model_iff (M : AlternatingProductModel L z r 6)
    (e : L ≃* alternatingGroup (Fin 6)) :
    Function.Surjective (modelNormalizerAction M) ↔ FullAutomorphismCase e :=
  modelNormalizerAction_surjective_iff M e

/-- The image alternative, with the full case expressed in the caller's coordinates.
The ambient strengthening is `overgroup_dichotomy`. -/
theorem normalizer_image_alternative (M : AlternatingProductModel L z r 6)
    (e : L ≃* alternatingGroup (Fin 6)) :
    (modelNormalizerAction M).range = AlternatingSix.ShadowLocal.natural ∨
      FullAutomorphismCase e :=
  (modelNormalizerAction_range_alternative M).imp id ((fullAutomorphismCase_model_iff M e).mp)

variable [Finite G] {T : Sylow 2 G} {g : G} {R : Subgroup G}

/-- Construct all the shared local geometry for source 16.4.9(2) in the original
T and L. The product exclusions follow from the constructed conjugate overgroups;
the stabilizer calculation does not use total-product fusion or transitivity. -/
theorem exists_local_geometry
    (h : IntersectionSetup T z L g R)
    (hTC : commutingSylow T L = zpowers z) (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hsmall : OrderTwoOutsideDeltaZero L) (hempty : ¬ (deltaZero L).Nonempty)
    (e : L ≃* alternatingGroup (Fin 6)) (M : AlternatingProductModel L z r 6) :
    ∃ M' : AlternatingProductModel L z r 6,
      elementary M' ≤ (T : Subgroup G) ∧
      MarkedOvergroups M' ∧
      IsConj z r ∧
      ProductExclusions M' ∧
      (L ⊔ (T : Subgroup G) = AlternatingOvergroup L z r ∨ FullAutomorphismCase e) ∧
      Nat.card (normalizerStabilizer M') = 6 := by
  have hconj := conjugate_outer h hTC hr hr2
  obtain ⟨M', hplace, hmarked⟩ := MarkedPlacement.exists_marked_placement h hTC hr hr2 M
  have hex := productExclusions_of_markedOvergroups h.toStandardSetup hsmall hempty e M'
    hconj hmarked
  exact ⟨M', hplace, hmarked, hconj, hex,
    overgroup_dichotomy h.toStandardSetup (h.le_sylow hr) hTC e M',
    normalizerStabilizer_card h.toStandardSetup M' hconj hex⟩

end CFSG.Quasithin.Chapter16.Intersections.Six
