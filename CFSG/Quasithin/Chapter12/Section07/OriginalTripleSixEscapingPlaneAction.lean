module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixEscapingThreeSpace
public import Theory.Representation.HexacodeAction.FullPlaneAction

/-!
# The original escaping involution on the actual six full-weight planes

The exact original corank-three theorem supplies the outer local involution.
Its fixed subgroup has no full-weight point, because every such point has
contained centralizer. In the same chosen chart the involution therefore
acts without fixed points on the six literal full-weight scalar planes.
Its cycle type there is 2^3. No coordinate-six identification is used.

Source: Aschbacher--Smith, 12.7.10(5), printed p.843.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource Atlas.Codes
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The genuine original escaping actor has cycle type 2^3 in the action
on the six full-weight planes of the unchanged chosen module. -/
theorem original_tripleSix_escaping_six_plane_action
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (contained : centralizer ({(t : G)} : Set G) ≤ normalizer (K : Set G))
    (W : Subgroup G) (hWU : W ≤ U) (hcor : subgroupCorank U W = 3)
    (hescape : ¬ centralizer (W : Set G) ≤ normalizer (K : Set G)) :
    ∃ b : Automizer U, b ≠ 1 ∧ b ^ 2 = 1 ∧ b ∉ inducedAutomizer U K ∧
      (∀ u : U, b.val u = u ↔ (u : G) ∈ W) ∧
      inducedAutomizer U (normalizer (K : Set G) ⊓ centralizer (W : Set G)) =
        zpowers b ∧
      ∃ f : Automizer U →* HexAutomorphisms, Function.Injective f ∧
        (inducedAutomizer U K).map f = hexSign.ker ∧
        (∀ (d : Automizer U) (u : U),
          (tripleSixPointCoordinates D a (d.val u)).toAdd =
            Hexacode.action (f d) (tripleSixPointCoordinates D a u).toAdd) ∧
        (Hexacode.fullPlanePerm (f b)).cycleType = {2, 2, 2} := by
  obtain ⟨b, hbne, hb2, hbout, hbfix, hB⟩ :=
    original_tripleSix_escaping_threeSpace h structural D a t ht heven contained
      W hWU hcor hescape
  obtain ⟨f, hf, _, hK, heq⟩ := original_tripleSix_full_automizer h structural D a
  refine ⟨b, hbne, hb2, hbout, hbfix, hB, f, hf, hK, heq, ?_⟩
  apply Hexacode.fullPlanePerm_cycleType_of_no_full_weight_fixed (f b)
    (by rw [← map_pow, hb2, map_one])
  intro v hv hweight
  let c := tripleSixPointCoordinates D a
  obtain ⟨u, hu⟩ := c.surjective (Multiplicative.ofAdd v)
  have hbu : b.val u = u := by
    apply c.injective
    change (c (b.val u)).toAdd = (c u).toAdd
    rw [hu]
    have hh := heq b u
    change (c (b.val u)).toAdd = Hexacode.action (f b) (c u).toAdd at hh
    rw [hu] at hh
    exact hh.trans hv
  have huW := (hbfix u).mp hbu
  have hw : hammingNorm (c u).toAdd.val = 6 := by rw [hu]; exact hweight
  exact hescape ((centralizer_le (Set.singleton_subset_iff.mpr huW)).trans
    (original_tripleSix_full_weight_centralizer_le D a t ht heven contained u hw))

end CFSG.Quasithin.Chapter12.Section07
