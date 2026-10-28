module

public import Theory.GroupTheory.GeneralizedFitting.SolvableNormalKernel
public import Theory.GroupTheory.SelfCentralizingCore

/-!
# Excluding ordinary components

A solvable group has no nontrivial perfect subgroup. A finite group with a
self-centralizing two-core also has no component: each component lies in or
centralizes that solvable normal subgroup.

Source: the component normal-subgroup dichotomy (GLS, volume 2, Theorem 3.5).
-/

public section
open Subgroup
namespace Theory.GroupTheory

/-- Solvability excludes every ordinary component. -/
theorem not_isComponent_of_solvable {H : Type*} [Group H] [Group.IsSolvable H]
    (D : Subgroup H) : ¬ IsComponent H D := by
  intro hD
  let := hD.2
  let : IsSimpleGroup (D ⧸ center D) := IsQuasisimple.simple
  let : Nontrivial D := (QuotientGroup.mk'_surjective (center D)).nontrivial
  exact Group.IsPerfect.not_isSolvable D inferInstance

/-- A self-centralizing two-core excludes every ordinary component. -/
theorem not_isComponent_of_twoCore {H : Type*} [Group H] [Finite H]
    (h : centralizer (pCore 2 H : Set H) ≤ pCore 2 H) (D : Subgroup H) :
    ¬ IsComponent H D := by
  let : Group.IsNilpotent (pCore 2 H) := (pCore_isPGroup (p := 2) (G := H)).isNilpotent
  exact not_isComponent_of_solvable_normal_selfCentralizing (pCore 2 H) h D
end Theory.GroupTheory
