module

public import Theory.Representation.PSL3Two.IrreducibleCatalogue.FanoDecomposition.Transitive
public import Theory.Representation.BinaryOffender.PermutationConjugacy
public import Theory.SpecificGroups.PSL3Two.Parabolics.Subgroups.Bruhat

/-!
# Fixed vectors of a Sylow subgroup on the natural binary three-space

A Sylow two-subgroup of SL₃(2) fixes at most two vectors. For the upper
triangular Sylow, two elementary matrices already force the last two
coordinates to vanish. A checked eight-vector calculation counts these
solutions; Sylow conjugacy transports the bound to every Sylow subgroup.

This is the natural-module calculation used in Aschbacher–Smith,
*The Classification of Quasithin Groups*, Lemma J.2.1, printed p.432
(combined manuscript of 1 March 2004).
-/

@[expose] public section
noncomputable section
open Representation Representation.BinaryOffender
namespace BinaryLinearThree
open Matrix.PSL3Two FanoDecomposition

private theorem two_fixed_card :
    Fintype.card {v : Vector // W (Bruhat.upper 1) v = v ∧ W (Bruhat.upper 4) v = v} = 2 := by
  decide +kernel

/-- A Sylow two-subgroup fixes at most two vectors of the natural binary three-space. -/
theorem card_sylow_natural_fixed_le_two (P : Sylow 2 Group) :
    Nat.card (fixedSpace W (P : Subgroup Group)) ≤ 2 := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq Group flagSylow P
  have hP : ((g • flagSylow : Sylow 2 Group) : Subgroup Group) =
      borelSL.map (MulAut.conj g).toMonoidHom := by
    rw [Sylow.coe_subgroup_smul, flagSylow_coe, markedFlag_stabilizer]
    rfl
  rw [hP, ← Nat.card_congr (fixedSpaceConjEquiv W borelSL g).toEquiv]
  let f : fixedSpace W borelSL →
      {v : Vector // W (Bruhat.upper 1) v = v ∧ W (Bruhat.upper 4) v = v} :=
    fun v => ⟨v, v.property ⟨_, Bruhat.upper_mem 1⟩, v.property ⟨_, Bruhat.upper_mem 4⟩⟩
  have hi : Function.Injective f := by
    intro x y h
    have he := congrArg Subtype.val h
    exact Subtype.ext he
  have hc := Nat.card_le_card_of_injective f hi
  have hh : Nat.card {v : Vector // W (Bruhat.upper 1) v = v ∧ W (Bruhat.upper 4) v = v} = 2 := by
    rw [Nat.card_eq_fintype_card, two_fixed_card]
  exact hc.trans_eq hh
end BinaryLinearThree
