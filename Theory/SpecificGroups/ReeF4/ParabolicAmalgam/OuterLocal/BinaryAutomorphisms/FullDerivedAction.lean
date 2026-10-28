module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.BinaryAutomorphisms.DerivedAction
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.BinaryAutomorphisms.FullDerivedAction.Center
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders
public import Theory.SpecificGroups.Tits.SharpOuterBound
public import Theory.GroupTheory.DerivedAutomorphismAction

/-!
# Reducing the full binary Ree action to concrete structural bounds

An identification of the derived subgroup with Parrott's certified simple
Tits group proves that the kernel of `binaryDerivedAction` is exactly the
center of `Model 0`. Faithfulness therefore reduces to triviality of the
center of the actual exceptional-twist fixed matrix group.

If that group is centerless and its derived subgroup is proper, the bound
`|Out(ParrottGroup)| ≤ 2` also proves coverage of every derived-subgroup
automorphism, by comparing the outer order with the ambient index. The
derived-group identification transports the actual outer quotient.

Properness also follows from any subgroup of order `4096`, since that
order does not divide the certified Tits order. This allows reuse of the
independent positive-root coordinate count, with no new global order proof.

The conditional reduction below keeps centerlessness, properness and the
outer-order bound explicit. The final theorem discharges them from the
concrete center, radical-order and sharp-outer-bound developments. In
particular, the two-group property of the Tits outer quotient alone is
insufficient for the source identification `Aut(²F₄(2)') = ²F₄(2)` used in
Aschbacher–Smith F.1.12, `refs/quasithin.pdf`, printed pp.263–264.
-/

public section

namespace ReeF4.Parabolics.OuterLocal

open Subgroup

/-- The allowed derived-group comparison supplies its trivial center. -/
theorem binaryDerived_center_eq_bot
    (e : commutator (Model 0) ≃* Tits.ParrottGroup) :
    center (commutator (Model 0)) = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have he : e x ∈ center Tits.ParrottGroup := MulEquivClass.apply_mem_center e hx
  rw [Tits.parrottGroup_center_eq_bot, mem_bot] at he
  exact mem_bot.mpr (e.injective (he.trans e.map_one.symm))

/-- The actual derived action has precisely the full matrix group's center
as its kernel. The comparison alone does not show that this kernel is trivial. -/
theorem binaryDerivedAction_ker_eq_center
    (e : commutator (Model 0) ≃* Tits.ParrottGroup) :
    binaryDerivedAction.ker = center (Model 0) := by
  rw [MulAut.conjNormal_ker_eq_centralizer]
  exact centralizer_commutator_eq_center_of_center_eq_bot (binaryDerived_center_eq_bot e)

/-- Faithfulness is equivalent to the concrete center calculation. -/
theorem binaryDerivedAction_injective_iff_center_eq_bot
    (e : commutator (Model 0) ≃* Tits.ParrottGroup) :
    Function.Injective binaryDerivedAction ↔ center (Model 0) = ⊥ := by
  rw [← MonoidHom.ker_eq_bot_iff, binaryDerivedAction_ker_eq_center e]

/-- A subgroup of order `2^12` cannot lie in a group isomorphic to Tits,
whose order has two-part `2^11`. The positive-root count can supply this
subgroup without a separate calculation of the full Ree group order. -/
theorem binaryDerived_ne_top_of_subgroup_card_4096
    (e : commutator (Model 0) ≃* Tits.ParrottGroup)
    (U : Subgroup (Model 0)) (hU : Nat.card U = 4096) :
    commutator (Model 0) ≠ ⊤ := by
  intro htop
  have hc : Nat.card (Model 0) = 17971200 := by
    calc
      Nat.card (Model 0) = Nat.card (commutator (Model 0)) := by rw [htop, card_top]
      _ = Nat.card Tits.ParrottGroup := Nat.card_congr e.toEquiv
      _ = 17971200 := Tits.parrottGroup_card
  have hd := U.card_subgroup_dvd_card
  rw [hU, hc] at hd
  norm_num at hd

/-- Centerlessness, properness of the derived subgroup and the sharp Tits
outer bound imply both faithfulness and full automorphism coverage. These
three concrete premises must still be proved for the source assertion. -/
theorem binaryDerivedAction_bijective_of_center_proper_outer_bound
    (e : commutator (Model 0) ≃* Tits.ParrottGroup)
    (hc : center (Model 0) = ⊥)
    (hp : commutator (Model 0) ≠ ⊤)
    (ho : Nat.card (MulAut.Outer Tits.ParrottGroup) ≤ 2) :
    Function.Bijective binaryDerivedAction := by
  have hcentral : centralizer (commutator (Model 0) : Set (Model 0)) = ⊥ :=
    (centralizer_commutator_eq_center_of_center_eq_bot
      (binaryDerived_center_eq_bot e)).trans hc
  apply MulAut.conjNormal_bijective_of_outer_card_le_index _ hcentral
  calc
    Nat.card (MulAut.Outer (commutator (Model 0))) =
        Nat.card (MulAut.Outer Tits.ParrottGroup) :=
      Nat.card_congr (MulAut.outerCongr e).toEquiv
    _ ≤ 2 := ho
    _ ≤ (commutator (Model 0)).index := (commutator (Model 0)).one_lt_index_of_ne_top hp

/-- The actual full binary Ree group acts bijectively on the actual derived
subgroup. The derived comparison is the only model identification supplied as
an explicit input; centerlessness, properness and the sharp Tits outer bound
are all discharged by their concrete developments. -/
theorem binaryDerivedAction_bijective
    (e : commutator (Model 0) ≃* Tits.ParrottGroup) :
    Function.Bijective binaryDerivedAction := by
  apply binaryDerivedAction_bijective_of_center_proper_outer_bound e
    binary_center_eq_bot
    (binaryDerived_ne_top_of_subgroup_card_4096 e (unipotent 0) ?_)
    Tits.SharpOuterBound.parrott_outer_card_le_two
  simpa using (card_unipotent 0)

end ReeF4.Parabolics.OuterLocal
