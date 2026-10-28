module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.TwentyFive.Inputs
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.TwentyFive.InnerInvolutions

/-!
# The remaining PSL₂(25) exclusion calculations

Inner involutions move at least six dimensions. A small actor containing one
therefore has rank three and exactly that involution's fixed space. An actual
inner order-three product of two actors conjugate inside its centralizer would
fix this six-codimensional space. The uniform order-three displacement bound
eight contradicts this. Cyclic actors instead give degree at most eight from
four conjugate generators, contradicting the torus-prime lower bound twelve.

This assembly retains the full source action, field and diagonal actors, and
the original representation. The two Inputs predicates remain explicit missing
calculations; the unconditional exclusion is not asserted. A uniform lower
bound eight removes the need for the source's degree-twelve representation
calculation, but it must itself be proved from the actual Borel action.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 4.1,
manuscript pp.8--9; Aschbacher--Smith K.2, printed p.453.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.TwentyFive
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender

universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (h : SourceAction ρ)
include h

/-- Every small actor containing an inner involution has rank three and the
same fixed space as that involution. This requires no degree upper bound. -/
theorem source_actor_saturation_of_inner
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 25)
    {A : Subgroup G} (hA : IsElementaryTwo A)
    (hsmall : fixedCodim ρ A ≤ 2 * rank A)
    {t : G} (htA : t ∈ A) (htL : t ∈ generalizedFitting G) (ht : orderOf t = 2) :
    rank A = 3 ∧ fixedCodim ρ A = 6 ∧
      fixedSpace ρ A = fixedSpace ρ (zpowers t) :=
  source_twentyFive_actor_saturation ρ h hm hA hsmall htA
    (source_inner_displacement_ge_six ρ h hm htL ht)

/-- The strict source exclusion follows from two independent calculations.
Their proofs remain with the actor-geometry and order-three-displacement owners;
this theorem does not assert either calculation. -/
theorem source_exclusion_of_calculations
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 25)
    (hgeometry : ActorGeometry G) (hthree : ThreeDisplacementBound ρ) :
    2 < cubicRatio ρ := by
  by_contra hn
  have hq : cubicRatio ρ ≤ 2 := le_of_not_gt hn
  obtain ⟨A, hA, _, hsmall⟩ := (cubicRatio_le_nat_iff ρ 2).mp hq
  rcases hgeometry A hA with ⟨hr, t, htA, _, g, hgen⟩ |
    ⟨t, htA, htL, ht2, hprod⟩
  · have hup := RankOneSize.degree_le_of_actor_conjugates ρ h hsmall hr.le htA g hgen
    have hlo := twelve_le_degree_twentyFive ρ h.faithful hm
    norm_num at hup
    omega
  · have hlo := source_inner_displacement_ge_six ρ h hm htL ht2
    obtain ⟨hr, _, _⟩ := source_actor_saturation_of_inner ρ h hm hA hsmall htA htL ht2
    obtain ⟨g, a, hgL, haA, haL, hgt, horder⟩ := hprod hr
    have hxL : a * (g * a * g⁻¹) ∈ generalizedFitting G :=
      (generalizedFitting G).mul_mem haL
        ((generalizedFitting G).mul_mem ((generalizedFitting G).mul_mem hgL haL)
          ((generalizedFitting G).inv_mem hgL))
    have hlarge := hthree _ hxL horder
    exact source_twentyFive_not_small_actor_of_product ρ h hm hA htA hlo
      hgt haA haA (by omega) hsmall

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.TwentyFive
