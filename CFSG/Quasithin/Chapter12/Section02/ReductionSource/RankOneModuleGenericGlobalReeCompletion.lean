module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalReeCompletion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalReeOvercomponent

/-!
# General Ree local completion geometry for the original Chapter12 pair

The actual prepared whole-residual pair has the marked linear/Suzuki
completion on L ∨ O²(H), with full Borel overlap, local valences, nine-path
transitivity and girth at least sixteen. Its parameter is the original
n = 2m+1, and m is positive. Both supplied comparison orientations are retained;
the impossible orientation is discharged by the existing local exclusion.

This is the actual-consumer application of the local geometric increment.
Ambient generation, the source order comparison and recognition remain in
this theorem family before a GlobalExit theorem can be supplied.
Source: Aschbacher–Smith 5.3.1–4 and the Chapter12 application,
printed pp.658–659,795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
open ChapterF.SourceCompletion.GeneralReeFour
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The actual Chapter12 prepared Ree row has the marked nine-path completion
geometry on the original perfect factor join. -/
theorem rankOne_global_ree_completion_geometry
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ)
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (ReeFour.amalgam m)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (ReeFour.amalgam m).reverse)) :
    2*m+1 = n ∧ 0 < m ∧
    (normalizer (L : Set G) ⊔ normalizer (residual H : Set G) ≤
      normalizer ((L ⊔ residual H : Subgroup G) : Set G)) ∧
    centralizer ((L ⊔ residual H : Subgroup G) : Set G) = ⊥ ∧
    ∃ e : RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (ReeFour.amalgam m).reverse,
    ∃ c : Completion m (L ⊔ residual H : Subgroup G),
      (∀ x, (c.left x : G) = (e.left.symm x : G)) ∧
      (∀ x, (c.right x : G) = (e.right.symm x : G)) ∧
      c.middle.range = (ChapterF.Source.commonBorel ![L,residual H] (Global.sourceS L H)).subgroupOf
        (L ⊔ residual H) ∧
      c.left.range ⊓ c.right.range = c.middle.range ∧
      c.graph.Connected ∧
      (∀ v : c.Vertex, SimpleGraph.PathTransitivePolygon.RootPathTransitive c.graph
        (L ⊔ residual H : Subgroup G) v 9) ∧
      (∀ v : c.Vertex, Nat.card (c.graph.neighborSet v) =
        (if v.type then (2^n)^2 else 2^n) + 1) ∧
      (∀ v : c.Vertex, ∀ p : c.graph.Walk v v, p.IsCycle → 16 ≤ p.length) := by
  exact d.ree_completion_geometry
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m he

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
