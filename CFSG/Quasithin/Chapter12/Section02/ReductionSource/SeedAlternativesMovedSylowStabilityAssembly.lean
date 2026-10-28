module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedSylowStability
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedSylowLinearThreeAssembly

/-!
# The two-summand Sylow orbit in every moved source row

The marked model list gives two unchanged-actor types in the natural rows.
In the triple-six and exterior-five rows, the same cubic actor stabilizes
every constituent and is best on each, so the common codimension budget
excludes a third constituent. This completes D.3.5(4) on the literal chosen
seed, without an exceptional-row exclusion hypothesis. The source 3.2.5
consumer retains the original moving element, disjointness and unchanged-L
nonisomorphism.

Exceptional-model exclusion and full-normalizer exhaustion remain with
qt-baumann-fsu; this module does not assert the full source 3.2.5 theorem.
Source: Aschbacher--Smith D.3.5(4), 3.2.5 and 12.2.2, combined manuscript
of 1 March 2004, printed pp.195--196,580,794--795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter3.Section02.ChosenSource325 ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The local cubic bound gives exactly two literal constituent types in
all moved B.4.2 rows, including the two exceptional rows before exclusion. -/
theorem sylowTwoModuleTypes_of_moved (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hq : cubicRatio D.orbitRepresentation ≤ 2)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G)) : D.SylowTwoModuleTypes := by
  rcases D.seed_constituentModel_or_exceptional_of_ff h hc hm
    (D.seed_ff_of_moved h hq hc hm) with hmodel | hex
  · exact D.sylowTwoModuleTypes_of_constituentModel h.quasisimple hc hm hmodel
  · exact D.sylowTwoModuleTypes_of_exceptional h hq hc hm hex

/-- D.3.5(4) for the original chosen subgroups, with the disjointness and
unchanged-L nonisomorphism needed by 3.2.5 retained. -/
theorem sylow_pair_of_moved_of_many (D : ChosenModule T L V)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G)) :
    ∃ t ∈ (T : Subgroup G), t ∉ normalizer (V : Set G) ∧
      componentOrbit V (T : Subgroup G) = V ⊔ V.map (MulAut.conj t).toMonoidHom ∧
      V ⊓ V.map (MulAut.conj t).toMonoidHom = ⊥ ∧
      ¬ SameConjugationModule L V (V.map (MulAut.conj t).toMonoidHom) := by
  have hq := D.orbit_cubicRatio_le_of_many h hmany
  obtain ⟨t,ht,hnt,htypes⟩ := D.sylowTwoModuleTypes_of_moved h.toHypothesis1221 hq hc hm
  exact ⟨t,ht,hnt,D.sylowOrbit_eq_sup_of_two_module_types t ht htypes,
    D.moved_conjugate_inf_eq_bot h.toHypothesis1221 hc ht hnt,
    D.moved_conjugate_not_sameModule ht hnt⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
