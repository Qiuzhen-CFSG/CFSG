module

public import Theory.GroupTheory.PerfectSmallSylowTwo
public import Theory.SpecificGroups.Janko1.Model.SylowTwo

/-!
# Central two-cores of perfect subgroups of the actual J₁ model

Every two-subgroup of the certified matrix model lies in a Sylow subgroup
of order eight. Thus a perfect subgroup has central two-core by the general
small-Sylow argument. The ambient commutator theorem retains the original
subgroup inclusion and embedded two-core.

This is the J₁ local inspection used in Aschbacher–Smith C.3.3, printed p.149
of `refs/quasithin.pdf`, to exclude a perfect projection with noncentral
two-core in an exchanged ordinary component.
-/

namespace Janko1
open Subgroup

/-- Every perfect subgroup of the actual J₁ model has central two-core. -/
public theorem perfect_subgroup_pCore_two_le_center
    (P : Subgroup Model) [Group.IsPerfect P] : pCore 2 P ≤ center P := by
  let S : Sylow 2 P := Classical.choice inferInstance
  obtain ⟨T, hST⟩ := (S.isPGroup'.map P.subtype).exists_le_sylow
  have hS : Nat.card S ≤ 8 := by
    have hc := Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hST)
    rw [Subgroup.card_map_of_injective P.subtype_injective, SylowTwo.card T] at hc
    exact hc
  exact pCore_two_le_center_of_isPerfect_of_sylow_card_le_eight S hS

/-- The two-core commutator vanishes in the original J₁ ambient group. -/
public theorem commutator_pCoreIn_eq_bot_of_isPerfect
    (P : Subgroup Model) [Group.IsPerfect P] : ⁅P.pCoreIn 2, P⁆ = ⊥ := by
  have he : ⁅pCore 2 P, (⊤ : Subgroup P)⁆ = ⊥ :=
    commutator_top_right_eq_bot_iff_le_center.mpr (perfect_subgroup_pCore_two_le_center P)
  have hm := congrArg (Subgroup.map P.subtype) he
  simpa only [map_commutator, ← MonoidHom.range_eq_map, range_subtype,
    Subgroup.map_bot, pCoreIn] using hm

end Janko1
