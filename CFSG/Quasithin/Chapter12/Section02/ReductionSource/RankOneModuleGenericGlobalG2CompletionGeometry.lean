module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2CompletionGeometry
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalG2Generation

/-!
# The original G₂ pair: coset geometry and a concrete recognition reduction

The prepared Chapter12 pair has seven-path transitivity and girth at least
twelve, retaining both actual parabolic maps and their whole common Borel.
The canonical Weyl relation then yields an isomorphism from ambient G to
the octonion G₂ model, and hence GlobalExit at the original exponent n>1.
No geometric or group-recognition certificate is assumed.

The Weyl relation, exhaustive comparison and original uniqueness remain
explicit source obligations. This conditional G₂ branch does not prove
5.2.3 or exhaust its other Lie and Mathieu alternatives.
Source: Aschbacher–Smith F.3.3–6, F.4.6–8, pp.270–278, and 5.3.3–4,
p.659, with the Chapter12 application on p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Atlas.G2
open SimpleGraph.PathTransitivePolygon
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open Global.G2CompletionGeometry
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The actual Chapter12 pair has seven-path transitivity and girth at least
twelve. Its exact compatible maps reduce recognition to their Weyl relation. -/
theorem rankOne_global_g2_completion_geometry
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse) :
    ∃ c : Global.G2CompletionGeometry.Completion F G,
      c.left = (ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 1).subtype.comp
        e.right.symm.toMonoidHom ∧
      c.right = (ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 0).subtype.comp
        e.left.symm.toMonoidHom ∧
      c.middle.range = ChapterF.Source.commonBorel ![L,residual H] (Global.sourceS L H) ∧
      c.left.range ⊓ c.right.range = c.middle.range ∧
      (∀ v, RootPathTransitive c.graph G v 7) ∧
      (∀ v (p : c.graph.Walk v v), p.IsCycle → 12≤p.length) ∧
      ((c.left nativeS*c.right nativeR)^6=1 → Nonempty (G ≃* Model F)) :=
  d.g2_ambient_completion_geometry (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F e

/-- An actual rank-two global output at the original exponent n>1. Only the
explicit canonical Weyl relation remains in this prepared G₂ branch. -/
theorem rankOne_globalExit_of_g2_weyl
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)
    (hweyl : ((e.right.symm (nativeS (F := F))).val *
      (e.left.symm (nativeR (F := F))).val)^6=1) : RankOneModule.GlobalExit G := by
  obtain ⟨hF,hiso⟩ := d.g2_ambient_recognition_of_weyl
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F e hweyl
  exact Or.inl ⟨n,hn,ClassificationModels.IsRankTwoModel.g2 hn
    ⟨F,inferInstance,inferInstance,hF,hiso⟩⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
