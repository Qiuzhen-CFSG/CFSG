module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor.Orbit.Source318
public import CFSG.Quasithin.Chapter3.Section01.Source318Guarded

/-!
# The chosen-module orbit bound with the standing guard retained

The original orbit is reduced, has the literal Sylow centralizer from the
Fundamental Setup, and has the genuine unique maximal local normalizer.
Apply the guarded 3.1.8 implication at that normalizer, using an actual
outside maximal local. The original intrinsic quotient action then gives
the cubic bound on the whole chosen-module orbit.

This uses only the guarded earlier source theorem. In particular it does
not construct the false unguarded universal 3.1.8 interface.
Source: Aschbacher--Smith 3.1.8(1), 3.2.5 and 12.2.2, pp.576,580,794--795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The exact whole-orbit bound, retaining both the guarded source theorem
and the independently supplied standing two-maximal condition. -/
theorem orbit_cubicRatio_le_of_guarded_source318 (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h318 : Chapter3.GuardedSourceTheorem318One G)
    (hout : ∀ M : Subgroup G, IsMaximalTwoLocal M → (T : Subgroup G) ≤ M →
      Chapter3.HasMaximalOutside T M) : cubicRatio D.orbitRepresentation ≤ 2 := by
  let H := L ⊔ (T : Subgroup G)
  let Q := ReducedNormal.intrinsicSubspace H D.orbitSpace
  have hW : (⊤ : Subgroup H) ≤ subspaceStabilizer (ReducedNormal.representation H)
      D.orbitSpace := orbitSpan_invariant _ ⊤ D.space
  have hr : IsPReduced 2 Q := by
    change IsPReduced 2 (ReducedNormal.intrinsicSubspace H D.orbitSpace)
    rw [ReducedNormal.intrinsicSubspace_eq]
    exact ReducedNormal.subspaceImage_isPReduced_of_action_core H D.orbitSpace hW
      (D.orbit_twoCore_eq_bot h)
  let := hr.normal
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
      (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
      (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
      h.simpleQTKE T h.maximal_faithful.1
  have hn : (L.subgroupOf (normalizer (L : Set G))).Normal :=
    normal_subgroupOf_of_le_normalizer le_rfl
  have he : componentOrbit L (T : Subgroup G) = L := D.localOrbit_eq
  have hm : IsMaximalTwoLocal (normalizer (L : Set G)) := by
    simpa only [he] using hu.normalizer_maximal
  have hj : H ≤ normalizer (L : Set G) := by
    simpa only [he] using hu.normalizer_contains
  have huniq : ∀ N : Subgroup G, IsMaximalTwoLocal N → H ≤ N →
      N = normalizer (L : Set G) := by
    simpa only [he] using hu.normalizer_unique
  have ht : (T : Subgroup G) ≤ normalizer (L : Set G) := le_sup_right.trans hj
  have hat := Chapter3.sourceTheorem318OneAt_of_guarded h318 hm ht
    (hout _ hm ht)
  have hb := hat.cubicRatio_le L h.maximal_faithful.2.1.2.1 L.le_normalizer hn hm hj huniq
    Q hr (D.orbit_intrinsic_centralizer h)
  exact ReducedNormal.cubicRatio_image_le_of_intrinsic_quotient H D.orbitSpace hW 2 hb

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
