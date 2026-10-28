module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Normalizers
public import CFSG.Quasithin.Chapter3.Section01.StandingGuard.Cardinality
public import CFSG.Quasithin.Chapter6.SourceDefs

/-!
# The two source exits needed by the Chapter 12 rank-one branch

The source acts on the whole R₂(LT), before T-invariance of the chosen
Irr⁺ section has been established. Its module conclusion concerns [R₂(LT),L].
The global alternatives below are actual isomorphisms, with the excluded
rank-two exponent strictly greater than one.

`GenericExit` and `SmallExit` are explicit unproved inputs to the conditional
assembly, not assertions of the book theorems. The generic producer must keep
5.2.3(1), including its exceptional centralizer configuration, and may merge
its module conclusion with the module exit. It must not infer n(H) = 1 from
that alternative. The small producer includes the earlier natural-module
reduction and both branches of the M₂₂ recognition argument.

Source: Aschbacher--Smith, 5.2.3 and 6.2.19--20, pp.649 and 690--691;
the application is 12.2.2(3d), p.795. No later Chapter 13 result is used.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The entire reduced subgroup, with its original ambient inclusion. -/
abbrev wholeReduced (T : Sylow 2 G) (L : Subgroup G) : Subgroup G :=
  (ReducedModule (L ⊔ (T : Subgroup G))).map (L ⊔ (T : Subgroup G)).subtype

/-- The literal commutator layer to which the earlier source result applies. -/
abbrev commutatorLayer (T : Sylow 2 G) (L : Subgroup G) : Subgroup G :=
  ⁅wholeReduced T L, L⁆

/-- Only concrete global models excluded by Hypothesis 12.2.3. -/
def GlobalExit (G : Type u) [Group G] : Prop :=
  (∃ f : ℕ, 1 < f ∧ ClassificationModels.IsRankTwoModel G f) ∨
    Nonempty (G ≃* Sporadic.Mathieu.M22) ∨ Nonempty (G ≃* Sporadic.Mathieu.M23)

/-- The specialized module/global consequence of 5.2.3, retaining its
exceptional module case. This is an input awaiting its source proof. -/
def GenericExit (T : Sylow 2 G) (L : Subgroup G) : Prop :=
  Chapter3.HasMaximalOutside T (normalizer (L : Set G)) →
    ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      1 < ChapterE.generationParameter H →
        Chapter6.Source.IsOneOrTwoA5Modules L (commutatorLayer T L) ∨ GlobalExit G

/-- The complementary source recognition implication. The bound ≤ 1 is
intentional: its producer must justify positivity when applying 6.1.1.
This is an input awaiting the natural reduction and recognition proof. -/
def SmallExit (T : Sylow 2 G) (L : Subgroup G) : Prop :=
  Chapter3.HasMaximalOutside T (normalizer (L : Set G)) →
    (∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      ChapterE.generationParameter H ≤ 1) →
    ¬ Chapter6.Source.IsOneOrTwoA5Modules L (commutatorLayer T L) →
      Nonempty (G ≃* Sporadic.Mathieu.M22)

end RankOneModule

namespace ChosenModule
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
include D

omit [Finite G] in
/-- Full commutator generation places the original choice in the whole layer. -/
theorem le_rankOne_commutatorLayer : V ≤ RankOneModule.commutatorLayer T L := by
  rw [D.eq_commutator]
  exact commutator_mono D.le_reduced le_rfl

omit [Finite G] in
/-- The whole layer is nontrivial before normalizing or reducing V. -/
theorem rankOne_commutatorLayer_ne_bot : RankOneModule.commutatorLayer T L ≠ ⊥ := by
  intro he
  exact D.ne_bot (bot_unique (he ▸ D.le_rankOne_commutatorLayer))

/-- The actual multiple-overgroup hypothesis supplies the outside local
at the component's normalizer, using the proved source uniqueness theorem. -/
theorem rankOne_hasMaximalOutside_of_many
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    Chapter3.HasMaximalOutside T (normalizer (L : Set G)) := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    h.simpleQTKE T h.maximal_faithful.1
  have he : componentOrbit L (T : Subgroup G) = L :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer L T L le_rfl
      D.sylow_normalizes_component) (le_componentOrbit L T)
  exact Chapter3.hasMaximalOutside_of_many T hmany _
    (he ▸ hu.normalizer_maximal) D.sylow_normalizes_component

end ChosenModule
end CFSG.Quasithin.Chapter12.Section02
