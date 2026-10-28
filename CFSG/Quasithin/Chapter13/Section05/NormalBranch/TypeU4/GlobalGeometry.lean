module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.TypeU4.NaturalGeometry
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceGlobal
/-!
# Global cubic geometry in the original Chapter13 normal branch

The original natural setup constructs IsType. Its original cubic component
is now the whole graph, and its stabilizer is the whole ambient group.
This discharges the global connectedness and order steps in the Asc94
application of13.5.16. Recognition of the concrete PSU₄(3) carrier remains
a separate obligation; the earlier13.5.15 source conclusions are retained.
Source: Aschbacher–Smith,13.5.16, pp.921–922; Asc94,45.10–45.11, pp.248–249.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.TypeU4
open Theory.GroupTheory.Recognition Section08.SourceCompletion
variable {G : Type*} [Group G] [Finite G]
  {D : ChapterF.Section09.Setup G} {V₂ M : Subgroup G} {g : G}

theorem global_geometry_of_natural_normal_branch
    (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
    (h : D.Hypothesis) (b : Conclusions D M 6 g) (hM : M = D.L)
    (z : G) (hz : z ∈ D.V₁) (hz1 : z ≠ 1)
    (P : Sylow 3 (UnitaryFourThree.centralizer z)) :
    Nat.card G=3265920 ∧ ∃ ht : UnitaryFourThree.IsType z,
      ∃ c : UnitaryFourThree.CubicGeometry.SourceConfiguration ht P,
        c.componentStabilizer=⊤ ∧ c.collinearity.Connected ∧ Nat.card c.points=280 ∧
        normalizer (c.W:Set G)⊔normalizer (c.V:Set G)=⊤ := by
  let ht := isType_of_natural_normal_branch d h b hM z hz hz1
  obtain ⟨c,hc,hconn,hcard,hgen,-⟩ := ht.original_cubic_global_geometry P
  exact ⟨ht.ambient_card,ht,c,hc,hconn,hcard,hgen⟩
end CFSG.Quasithin.Chapter13.Section05.NormalBranch.TypeU4
