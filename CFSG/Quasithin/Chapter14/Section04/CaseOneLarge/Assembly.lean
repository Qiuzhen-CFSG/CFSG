module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Preparation
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Contracts
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.MarkedSystem
public import CFSG.Quasithin.ChapterI.Section04To05.A3Recognition

/-!
# Conditional source assembly of the large extraspecial contradiction

The original chosen natural module constructs L₁ in Y and the natural flag.
The local action and the independently supplied second Y-member give all
three vertex quotients and parabolics. Restriction to their generated group
retains the original point vertex, whose core contains the nonzero chosen
module. The genuine I.5.8–9 incidence input then gives PSL₄(2) recognition,
and the existing order bound contradicts |U| > 64.

The local-action, marked-model partner and incidence implications are still
independent source obligations. These conditional consumers do not assert
14.4.14 while any of them remains explicit.

Source: Aschbacher--Smith, 14.4.8–13, pp.1009–1012; I.5.8–10, pp.421–422.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension LargerDimension.LocalAction LargerDimension.IntrinsicSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Assemble the three vertices from the two independent local source inputs.
No incidence or recognition conclusion is used in this construction. -/
noncomputable def source_marked_system (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (g : G) (hg : g ∈ L)
    (localData : LocalSourceData T L V F g)
    (X : Subgroup G) (hX : X ∈ YFamily F.H T (F.Vi 2) (F.E g))
    (hne : X ≠ F.Li L 1)
    (e₂ : coreQuotient (F.Li L 1 ⊔ X ⊔ (T : Subgroup G)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) :
    MarkedSystem L T (F.Li L 1) (F.Li L 2) X := by
  let h := higherRankHypothesis d earlier hq chosen
  have hN := source_natural_flag d earlier hq chosen structural F g hg
  have h₁ := source_first_actor d earlier hq chosen structural F g hg
  let a₁ := localData.action (F.Li L 1) h₁.1
  let aX := localData.action X hX
  let geo := source_geometry_of_full_actions F.H (normalizer (L : Set G)) L
    (F.Li L 1) (F.Li L 2) (F.Vi 1) (F.Vi 2) V (F.E g) X (F.I₂ L) T
    hN hX hne a₁ aX e₂ localData.unique L.le_normalizer
    (h.sylow_normalizes structural) le_rfl
  have eq₁ : Nonempty (coreQuotient (L ⊔ (T : Subgroup G)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) := by
    rw [← h₁.2.2]
    exact ⟨a₁.quotient⟩
  exact markedSystem_of_source_geometry L (F.Li L 1) (F.Li L 2) X
    (normalizer (L : Set G)) T geo eq₁ ⟨e₂⟩ ⟨aX.quotient⟩ localData.unique le_rfl

omit [Finite G] in
/-- The point-core premise of the genuine recognition endpoint is discharged
from the original chosen module, using the retained vertex equation. -/
theorem marked_point_core_nontrivial (chosen : ChosenModule T L V)
    (L₁ L₂ X : Subgroup G) (a : MarkedSystem L T L₁ L₂ X) : a.system.Q 0 ≠ ⊥ := by
  change (a.system.family 0).pCoreIn 2 ≠ ⊥
  rw [a.vertex_eq 0]
  exact source_point_core_nontrivial chosen (actualG0 L T L₁ L₂ X)
    (le_sup_left.trans le_sup_left)

omit [Finite G] in
/-- Recognition applies to the generated subgroup itself. Both its containment
of T and its actual PSL₄(2) equivalence are retained. -/
theorem recognized_overgroup_of_incidence (chosen : ChosenModule T L V)
    (L₁ L₂ X : Subgroup G) (a : MarkedSystem L T L₁ L₂ X)
    (incidence : Quasithin.I5.A3Recognition.GeometryData a.system) :
    (T : Subgroup G) ≤ actualG0 L T L₁ L₂ X ∧
      Nonempty (actualG0 L T L₁ L₂ X ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2)) :=
  ⟨source_T_le_actualG0 L T L₁ L₂ X,
    ⟨Quasithin.I5.A3Recognition.equivPSL4_of_geometry incidence
      (marked_point_core_nontrivial chosen L₁ L₂ X a)⟩⟩

/-- The final large-case consumer. The independent producers must supply
local action, a partner on the same literal E, and genuine incidence geometry.
The conjugator, first actor, core-free marked system, nontrivial point core,
recognized overgroup and numerical contradiction are constructed here. -/
theorem source_large_exclusion_of_inputs (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (localSource : ∀ g : G, g ∈ L → g ∈ F.P L → g ∉ F.H →
      Nonempty (LocalSourceData T L V F g))
    (partnerSource : ∀ g : G, g ∈ L → g ∈ F.P L → g ∉ F.H →
      LocalSourceData T L V F g → Partner T L V F g)
    (incidence : ∀ (K : Subgroup G) (S : Quasithin.I5.DSystem .A3 K), S.Q 0 ≠ ⊥ →
      Nonempty (Quasithin.I5.A3Recognition.GeometryData S)) : False := by
  obtain ⟨g, hg, hgP, hgH⟩ := exists_source_conjugator d earlier hq chosen structural F
  obtain ⟨localData⟩ := localSource g hg hgP hgH
  obtain ⟨X, hX, hXne, ⟨e₂⟩⟩ := partnerSource g hg hgP hgH localData
  let a := source_marked_system d earlier hq chosen structural F g hg localData X hX hXne e₂
  obtain ⟨geo⟩ := incidence (actualG0 L T (F.Li L 1) (F.Li L 2) X) a.system
    (marked_point_core_nontrivial chosen (F.Li L 1) (F.Li L 2) X a)
  obtain ⟨hTK, ⟨e⟩⟩ := recognized_overgroup_of_incidence chosen (F.Li L 1) (F.Li L 2) X a geo
  exact source_large_overgroup_exclusion d earlier hq chosen structural alternatives
    F hne hZ (by omega) _ hTK e

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
