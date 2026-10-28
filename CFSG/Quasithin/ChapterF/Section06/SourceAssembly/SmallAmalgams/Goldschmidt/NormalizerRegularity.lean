module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.NormalizerGeometry
public import Theory.GroupAction.CubicTree.RegularityExistence

/-!
# The original normalizer quotient has a regular arc length

The distance-two component of the track normalizer is a cubic tree, and
its component stabilizer modulo the literal track fixer acts faithfully.
The proved source geometry supplies local and vertex transitivity and finite
vertex stabilizers. Thus the generic regularity theorem applies to this
actual quotient and computes its local order.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (5.2),
printed p.394. The separate upper bound on the regularity length is not
part of this existence and cardinality result.
-/

public section
open Subgroup SimpleGraph
open Theory.GroupAction.CubicTree

namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

/-- The source normalizer quotient has a regularity length, with the exact
vertex-stabilizer order for the literal quotient action. -/
theorem normalizerQuotient_regularity (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G) (ht0 : t.vertex 0 = RankTwo.base F false)
    (hQ : NormalizerCandidate F (trackFixer t)) :
    letI := normalizerQuotientAction h t ht0
    ∃ s : ℕ, 0 < s ∧
      (∀ (k : ℕ) (x : normalizerComponent F (trackFixer t))
        (p : BasedWalk (normalizerComponent F (trackFixer t)).toSimpleGraph k x),
        k < s → p.Nonbacktracking →
          RightRegular (A := normalizerComponentQuotient F (trackFixer t)) p) ∧
      WeissEven.ArcFree (Γ := (normalizerComponent F (trackFixer t)).toSimpleGraph)
        (G := normalizerComponentQuotient F (trackFixer t)) s ∧
      ∀ x : normalizerComponent F (trackFixer t),
        Nat.card (MulAction.stabilizer (normalizerComponentQuotient F (trackFixer t)) x) =
          3 * 2 ^ (s - 1) := by
  let _ := normalizerQuotientAction h t ht0
  obtain ⟨htree, hcubic, hfaith, hact, hvertex, hlocal, hfinite⟩ :=
    normalizerQuotient_geometry h t ht0 hQ
  let _ : FaithfulSMul (normalizerComponentQuotient F (trackFixer t))
      (normalizerComponent F (trackFixer t)) := hfaith
  exact exists_arcRegularityLength hact htree.connected hcubic hvertex
    (fun {x y z} => hlocal x y z) hfinite

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
