module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.ArcSetup
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.ArcSingularity
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.UniversalSetup
public import Theory.GroupAction.CubicTree.SingularKernel

/-!
# Singular arc fixers in the original Goldschmidt action

The cubic valence and faithful universal action discharge the geometric
hypotheses of the kernel-propagation lemma. The conclusion concerns the literal
pointwise path stabilizer in the original acting group, as required for the
locally regular case of Goldschmidt's classification.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), remark after
(2.12), printed p.384, used in (4.3), printed p.392.
-/

@[expose] public section

open Subgroup SimpleGraph SimpleGraph.BasedWalk
open Theory.GroupAction.CubicTree

namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry

variable {G : Type*} [Group G] {F : Bool → Subgroup G}

/-- Cubic valence permits a continuation avoiding any one vertex. -/
theorem CubicTreeAction.hasTwoNeighbors (h : CubicTreeAction F) :
    HasTwoNeighbors (RankTwo.graph F) := by
  intro v w
  apply Set.exists_ne_of_one_lt_ncard
  change 1 < Nat.card ((RankTwo.graph F).neighborSet v)
  rw [h.card_neighbor v]
  decide

/-- When all arcs of the chosen positive length are totally singular, their
literal pointwise stabilizers in the original ambient group are trivial. -/
theorem CubicTreeAction.pathStabilizer_eq_bot_of_totallySingular
    (h : CubicTreeAction F) {s : ℕ} (hs : 0 < s)
    (hsing : ∀ (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) s v),
      p.Nonbacktracking → ∀ a : G, (∀ y ∈ p.vertices, a • y = y) →
      (∀ z, Theory.GroupAction.CubicTree.Forward p z → a • z = z) ∧
      (∀ z, Backward p z → a • z = z))
    {v : RankTwo.Vertex F} (p : BasedWalk (RankTwo.graph F) s v)
    (hp : p.Nonbacktracking) : RankTwo.pathStabilizer F p = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro a ha
  apply Subgroup.mem_bot.mpr
  let _ : FaithfulSMul G (RankTwo.Vertex F) :=
    ⟨fun heq => h.action_injective (Equiv.ext heq)⟩
  exact eq_one_of_all_totallySingular h.tree.connected.preconnected h.hasTwoNeighbors
    hs hsing p hp a ha

/-- The even first-singularity branch supplies total singularity itself, so
every arc at least as long has trivial literal pointwise stabilizer. -/
theorem CubicTreeAction.pathStabilizer_eq_bot_of_even
    (h : CubicTreeAction F) {s : ℕ} (hs : 0 < s) (heven : Even s)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F)
      (q : BasedWalk (RankTwo.graph F) k v),
      k < s → q.Nonbacktracking → RightRegular (A := G) q)
    {v : RankTwo.Vertex F} (p : BasedWalk (RankTwo.graph F) s v)
    (hp : p.Nonbacktracking) (hn : ¬ RightRegular (A := G) p)
    {n : ℕ} (hsn : s ≤ n) {w : RankTwo.Vertex F}
    (q : BasedWalk (RankTwo.graph F) n w) (hq : q.Nonbacktracking) :
    RankTwo.pathStabilizer F q = ⊥ := by
  apply h.pathStabilizer_eq_bot_of_totallySingular (p := q) (hp := hq)
    (lt_of_lt_of_le hs hsn)
  intro z r hr a ha
  exact h.totallySingular_of_even hs heven hshort p hp hn hsn r hr a ha

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
