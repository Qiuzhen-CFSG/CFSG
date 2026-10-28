module

public import CFSG.Quasithin.Chapter16.Section01To02.ComponentTransfer.Basic
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Mathlib.GroupTheory.Nilpotent

/-!
# Extracting components from the two-residual of a centralizer

A finite perfect subgroup lies in O²(H), since its image in a two-group
quotient is perfect and nilpotent, hence trivial. If O²(H) is quasisimple,
component maximality therefore identifies every component of H with O²(H).
The resulting equivalences retain the actual component, not just its quotient.
Solvable two-residuals and self-centralizing two-cores exclude components.

These are the group-theoretic operations used when inspecting the intrinsic
rows of 16.1.4–16.1.5. Here the residual is O²(C_K(t)); it is distinct from
both O₂(C_K(t)) and the solvable residual C_K(t)^∞. The concrete row and
exceptional-parameter calculations remain obligations of the source assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.4–16.1.5 and the proof of 16.1.7, pp.1171–1173.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.ComponentTransfer.Intrinsic

open Subgroup Theory.GroupTheory

variable {G : Type*} [Group G] [Finite G]

private theorem perfect_isPPerfect [Group.IsPerfect G] : IsPPerfect 2 G := by
  intro N hN hp
  let := hN
  have hsub : Subsingleton (G ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (G ⧸ N) hp.isNilpotent
  apply eq_top_iff.mpr
  intro g _
  exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)

/-- The embedded O²(C_K(t)) of 16.1.4, not the solvable residual. -/
def centralizerTwoResidual (K : Subgroup G) (t : G) : Subgroup G :=
  (pResidual 2 (centralizerIn K t)).map (centralizerIn K t).subtype

/-- Relative components lie in the two-residual of their overgroup. -/
theorem component_le_twoResidual {L H : Subgroup G} (hL : IsComponentIn L H) :
    L ≤ (pResidual 2 H).map H.subtype := by
  let := hL.2.2
  have hle := le_pResidual_of_isPPerfect (L.subgroupOf H) perfect_isPPerfect
  simpa only [map_subgroupOf_eq_of_le hL.1] using map_mono (f := H.subtype) hle

/-- A quasisimple two-residual is the unique component of its overgroup. -/
theorem component_eq_of_quasisimple_twoResidual {L H : Subgroup G}
    (hL : IsComponentIn L H)
    [IsQuasisimple ((pResidual 2 H).map H.subtype)] :
    L = (pResidual 2 H).map H.subtype := by
  let D := (pResidual 2 H).map H.subtype
  have hLD : L ≤ D := component_le_twoResidual hL
  have hc := hL.restrict hLD (map_subtype_le _)
  have ht : IsComponent D (⊤ : Subgroup D) :=
    ⟨.top, IsQuasisimple.of_mulEquiv Subgroup.topEquiv.symm⟩
  exact le_antisymm hLD (subgroupOf_eq_top.mp (hc.2.eq_of_le ht le_top))

/-- The component itself is isomorphic to the intrinsic two-residual. -/
noncomputable def componentEquivTwoResidual {L H : Subgroup G}
    (hL : IsComponentIn L H) [IsQuasisimple (pResidual 2 H)] : L ≃* pResidual 2 H := by
  let e := (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
  let := IsQuasisimple.of_mulEquiv e
  exact (MulEquiv.subgroupCongr (component_eq_of_quasisimple_twoResidual hL)).trans e.symm

/-- An intrinsic two-residual model identifies the actual component. -/
noncomputable def componentEquivModel {L H : Subgroup G} (hL : IsComponentIn L H)
    {M : Type*} [Group M] [IsQuasisimple M] (e : pResidual 2 H ≃* M) : L ≃* M := by
  let := IsQuasisimple.of_mulEquiv e.symm
  exact (componentEquivTwoResidual hL).trans e

/-- A solvable two-residual rules out relative components. -/
theorem no_component_of_solvable_twoResidual (H : Subgroup G)
    [Group.IsSolvable ((pResidual 2 H).map H.subtype)] :
    ¬ ∃ L, IsComponentIn L H := by
  rintro ⟨L, hL⟩
  let D := (pResidual 2 H).map H.subtype
  have hLD : L ≤ D := component_le_twoResidual hL
  have hc := hL.restrict hLD (map_subtype_le _)
  let := hc.2.2
  let : IsSimpleGroup ((L.subgroupOf D) ⧸ center (L.subgroupOf D)) :=
    IsQuasisimple.simple
  have : Nontrivial (L.subgroupOf D) :=
    (QuotientGroup.mk'_surjective (center (L.subgroupOf D))).nontrivial
  exact Group.IsPerfect.not_isSolvable (L.subgroupOf D) inferInstance

/-- A self-centralizing two-core rules out relative components. -/
theorem no_component_of_selfCentralizing_twoCore (H : Subgroup G)
    (hc : centralizer (pCore 2 H : Set H) ≤ pCore 2 H) :
    ¬ ∃ L, IsComponentIn L H := by
  rintro ⟨L, hL⟩
  let := hL.2.2
  let : IsSimpleGroup ((L.subgroupOf H) ⧸ center (L.subgroupOf H)) :=
    IsQuasisimple.simple
  have : Nontrivial (L.subgroupOf H) :=
    (QuotientGroup.mk'_surjective (center (L.subgroupOf H))).nontrivial
  have hle : L.subgroupOf H ≤ pCore 2 H := by
    rcases hL.2.normal_dichotomy (pCore 2 H) with hle | hcomm
    · exact hle
    · exact (commutator_eq_bot_iff_le_centralizer.mp hcomm).trans hc
  exact Group.IsPerfect.not_isNilpotent (L.subgroupOf H)
    ((pCore_isPGroup (p := 2) (G := H)).to_le hle).isNilpotent

end CFSG.Quasithin.Chapter16.ComponentTransfer.Intrinsic
