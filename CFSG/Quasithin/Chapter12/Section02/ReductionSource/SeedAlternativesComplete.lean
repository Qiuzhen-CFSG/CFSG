module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedExhaustionBinaryMultiplicity
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionBinaryCommutant

/-!
# The chosen-seed source3.2.5 alternatives and their Chapter12 application

A strict enlargement of the normalizer orbit would give exactly two copies
of the original binary natural-plus-dual local pair. Its literal component
centralizer would then have order dividing 36. The already proved three-rank
bound, trivial two-core and binary outer-automorphism calculation exclude
this, proving equality of the full normalizer and Sylow orbits in the moved
branch. Together with the fixed-space branch and the full marked D.3.10
constituent list, this completes the genuine source3.2.5 alternatives.

Both cubic bounds retain their original actions and the standing guard
derived from hmany. The SL3 central-cover conventions and separate A7
four-dimensional branch are unchanged. The structural Chapter12 consumer
retains only exclusion of MarkedDoubled, whose independent source proofs
and final assembly belong to qt-d-1222-source. No universal FSU theorem or
unconditional Chapter12 classification is asserted here.
Source: Aschbacher--Smith D.3.9--10,3.2.5 and12.2.2,
printed pp.199--204,580--581,794--795; refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter3.Section02.ChosenSource325 ChapterD
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The full normalizer orbit equals the Sylow orbit in the original moved
chosen-seed branch. All binary multiplicity and centralizer premises are
discharged on the literal action. -/
theorem normalizerOrbit_eq_of_moved_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G)) :
    componentOrbit V (normalizer (L : Set G)) = componentOrbit V (T : Subgroup G) := by
  by_contra hne
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let : AddCommGroup (Additive U) := inferInstance
  let : Module (ZMod 2) (Additive U) := inferInstance
  let hn := le_normalizer_componentOrbit V M
  let ρ := UniqueFactor.imageRepresentation M U hn
  let K := (L.subgroupOf M).map (internalHom M U hn)
  obtain ⟨d,hd,⟨a⟩⟩ := D.normalizer_double_naturalDual_of_strict h hmany hc hm hne
  have hcard : Nat.card (centralizer (K : Set (internalActionImage M U hn))) ∣ 36 :=
    binary_double_component_centralizer_card_dvd ρ
      (UniqueFactor.imageRepresentation_injective M U hn) K (by omega : 3 ≤ d) a
  exact (D.normalizer_strict_binary_centralizer_obstruction h hmany hc hm hne).2.2 hcard

/-- The genuine qualitative source3.2.5 alternatives on the literal chosen
seed. The full-normalizer exhaustion, fixed-space implication, numerical
bounds and marked moved classification have all been proved. -/
theorem source325_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    D.Source325Alternatives := by
  apply D.source325_of_exhaustion_of_many h hmany
  intro _ _ hc hm _
  exact D.normalizerOrbit_eq_of_moved_of_many h hmany hc hm


/-- Both original numerical conclusions accompany the source alternatives.
The standing guard is supplied by the actual multiple-overgroup hypothesis. -/
theorem source325_with_bounds_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    cubicRatio D.orbitRepresentation ≤ 2 ∧
      D.NormalizerOrbitCubicBound h.toHypothesis1221 ∧ D.Source325Alternatives :=
  ⟨D.orbit_cubicRatio_le_of_many h hmany,D.normalizerOrbit_cubicBound_of_many h hmany,
    D.source325_of_many h hmany⟩

/-- The original Chapter12 structural consumer now retains only exclusion
of the genuine marked doubled alternative. That separate source input is
owned by qt-d-1222-source and its non-FF/double-natural producers. -/
theorem structural_of_not_doubled_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hex : ¬ D.MarkedDoubled) :
    (T : Subgroup G) ≤ normalizer (V : Set G) ∧
    IsPReduced 2 (V.subgroupOf (L ⊔ (T : Subgroup G))) ∧
    (∀ g ∈ normalizer (L : Set G),
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V) ∧
    ((normalizer (L : Set G)) ≤ normalizer (V : Set G) ∨
      V ⊓ centralizer (L : Set G) = ⊥) :=
  D.structural_of_source325_of_not_doubled_of_many h hmany (D.source325_of_many h hmany) hex

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
