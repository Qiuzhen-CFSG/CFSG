module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.LowRank.Source
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.ActionModel

/-!
# The degree-five first bound and the low-rank degree-four reduction

E.3.32 and the original pure-intersection hypothesis impose both pure core
restrictions on the literal offender image. At image rank n-1, the common
fixed-space counting bound and the index-two layer show that n=4, the
inner image has rank two, and the image is not contained in the layer.
This excludes the remaining degree-five offender and proves its complete
conditional first weak-closure bound, using the constructed action model.
The degree-four reverse-action contradiction remains with this owner.
Source: Aschbacher--Smith, 12.1.8, printed pp.792--793 (PDF809--810).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender BinaryNaturalDual
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterE CFSG.Quasithin.ChapterH.NaturalDual
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.LowRank
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  (B : DoubledBranch T L V n)
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]

omit [Finite G] in
/-- The first-stage pure-intersection hypothesis controls both summands of
the actual core under the original inner actor. -/
theorem first_core_restrictions (M : B.MarkedAutomizerModel)
    (hp : B.PureIntersectionCentralizes) {g : G}
    (C : ConjugateConfiguration (componentOrbit V (T : Subgroup G)) g 1 n) :
    let I := inducedAutomizer (componentOrbit V (T : Subgroup G))
      (offenderNormalizer (componentOrbit V (T : Subgroup G)) g)
    (M.setup.natural ⊓ generatedCore (M.setup.representation.comp I.subtype) (n-2) ≤
      M.setup.fixed (I ⊓ componentLayer _)) ∧
    (M.setup.dual ⊓ generatedCore (M.setup.representation.comp I.subtype) (n-2) ≤
      M.setup.fixed (I ⊓ componentLayer _)) := by
  let W := componentOrbit V (T : Subgroup G)
  let I := inducedAutomizer W (offenderNormalizer W g)
  let J := I ⊓ componentLayer (Automizer W)
  have hn : 2 ≤ n := by rcases B.degree with rfl | rfl <;> decide
  have hnat (a : J) (u : Additive W) (hu : u ∈ M.setup.natural) :
      M.setup.representation a u ∈ M.setup.natural := by
    let e := M.setup.model.coordinates
    have he := ModelOrbits.MarkedGeometry.mem_natural_iff_of_marking e
      M.setup.naturalCoordinates M.setup.model.natural_marking
    rw [he, innerNatural_equivariant]
    change (innerNatural M.setup I).dual a (e u).2 = 0
    rw [(he u).mp hu, map_zero]
  have hdual (a : J) (u : Additive W) (hu : u ∈ M.setup.dual) :
      M.setup.representation a u ∈ M.setup.dual := by
    let e := M.setup.model.coordinates
    have he := ModelOrbits.MarkedGeometry.mem_dual_iff_of_marking e
      M.setup.model.dualCoordinates M.setup.model.dual_marking
    rw [he, innerNatural_equivariant]
    change innerNatural M.setup I a (e u).1 = 0
    rw [(he u).mp hu, map_zero]
  have hpN : M.setup.natural ⊓ subgroupSpace W (W.map (MulAut.conj g).toMonoidHom) = ⊥ := by
    rw [M.natural_eq]
    exact B.natural_intersection_eq_bot hp g C.noncentralizing
  have hpD : M.setup.dual ⊓ subgroupSpace W (W.map (MulAut.conj g).toMonoidHom) = ⊥ := by
    rw [M.dual_eq]
    exact B.dual_intersection_eq_bot M hp g C.noncentralizing
  rw [M.representation_eq] at hnat hdual
  constructor
  · change _ ≤ fixedSpace M.setup.representation J
    rw [M.representation_eq]
    exact pure_core_le_fixed C hn _ J inf_le_left hnat hpN
  · change _ ≤ fixedSpace M.setup.representation J
    rw [M.representation_eq]
    exact pure_core_le_fixed C hn _ J inf_le_left hdual hpD

/-- Image rank n−1 is possible only in degree four, with inner rank two
and an actor leaving the component layer. This is the exact remaining
reverse-action case of the first paragraph of 12.1.8. -/
theorem first_low_rank_profile (M : B.MarkedAutomizerModel)
    (hp : B.PureIntersectionCentralizes) {g : G}
    (C : ConjugateConfiguration (componentOrbit V (T : Subgroup G)) g 1 n)
    (hr : rank (inducedAutomizer (componentOrbit V (T : Subgroup G))
      (offenderNormalizer (componentOrbit V (T : Subgroup G)) g)) = n-1) :
    let I := inducedAutomizer (componentOrbit V (T : Subgroup G))
      (offenderNormalizer (componentOrbit V (T : Subgroup G)) g)
    n = 4 ∧ rank (I ⊓ componentLayer _) = 2 ∧ ¬ I ≤ componentLayer _ := by
  let W := componentOrbit V (T : Subgroup G)
  let I := inducedAutomizer W (offenderNormalizer W g)
  let := offender_inducedAutomizer_elementary W g
  have hcore := first_core_restrictions B M hp C
  have he : rank I - 1 = n-2 := by change rank I = n-1 at hr; omega
  have hbound : 2 * rank (I ⊓ componentLayer _) ≤ n := by
    apply inner_rank_bound_of_core M.setup I
    · rw [he]; exact hcore.1
    · rw [he]; exact hcore.2
  have hlo := rank_le_inner_rank_add_one M.setup I
  change rank I ≤ rank (I ⊓ componentLayer (Automizer W)) + 1 at hlo
  change rank I = n-1 at hr
  have hn : n = 4 := by rcases B.degree with hh | hh <;> omega
  have hj : rank (I ⊓ componentLayer (Automizer W)) = 2 := by omega
  refine ⟨hn,hj,?_⟩
  intro hI
  rw [inf_eq_left.mpr hI] at hj
  change rank I = 2 at hj
  omega

/-- The low-rank first-stage offender in degree five is impossible. -/
theorem five_first_low_rank_false (B : DoubledBranch T L V 5)
    (M : B.MarkedAutomizerModel) (hp : B.PureIntersectionCentralizes) {g : G}
    (C : ConjugateConfiguration (componentOrbit V (T : Subgroup G)) g 1 5)
    (hr : rank (inducedAutomizer (componentOrbit V (T : Subgroup G))
      (offenderNormalizer (componentOrbit V (T : Subgroup G)) g)) = 4) : False := by
  have hh := (first_low_rank_profile B M hp C hr).1
  omega

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.LowRank

open CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
include h D

/-- The complete degree-five conditional implication of 12.1.8, using the
compatible action model constructed from the literal quotient. -/
theorem doubledFive_globalW_gt_one_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 5) :
    letI := D.doubledOrbit_elementary h
    B.PureIntersectionCentralizes →
    0 < globalW (componentOrbit V (T : Subgroup G)) T →
    (5 : ℕ∞) ≤ globalR (componentOrbit V (T : Subgroup G)) →
    1 < globalW (componentOrbit V (T : Subgroup G)) T := by
  let := D.doubledOrbit_elementary h
  intro hp hw hr
  let M := D.doubled_markedAutomizerModel h B
  by_contra hf
  obtain ⟨g,_,_,C,hI,_⟩ :=
    D.doubledFive_first_rank_four_of_many_of_model h hmany B M hp hw hr hf
  exact WeakClosure.LowRank.five_first_low_rank_false B M hp C hI

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
