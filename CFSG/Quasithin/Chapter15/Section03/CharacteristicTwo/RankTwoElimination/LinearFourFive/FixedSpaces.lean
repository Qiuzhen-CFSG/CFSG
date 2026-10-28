module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.ModuleCases
public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Modules

/-!
# The exact central submodule in the natural alternatives

Surjectivity of the component's natural action reduces fixed vectors to
fixed vectors for the full binary linear group. Both the natural space
and its contragredient have zero fixed space. Consequently each of the
two module alternatives has `C_{U_L}(L) = 1` as an equality of actual
ambient subgroups. This does not assert `C_{W_L}(L) = 1`: that larger
central summand must be retained in extension and projection arguments.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
the `Z_L` projection in 15.3.24, printed p.1129 (PDF p.1146).
-/

@[expose] public section

open Subgroup BinaryLinear.OuterCyclic
open BinaryNaturalDual.VectorStabilizers

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive

variable {G : Type*} [Group G] {d : LocalData G} {L : Subgroup G}

private theorem action_fixed (u : spanCommutator d L)
    (hu : (u : G) ∈ centralizer (L : Set G)) (l : L) :
    commutatorAction d L l u = u := by
  apply Subtype.ext
  change (l : G) * (u : G) * (l : G)⁻¹ = (u : G)
  rw [hu l l.property, mul_inv_cancel_right]

/-- Repeated natural summands have no central submodule, with any
multiplicity and either choice of the natural-module marking. -/
theorem RepeatedNatural.centralizer_eq_bot {r : ℕ} (h : RepeatedNatural d L r) :
    spanCommutator d L ⊓ centralizer (L : Set G) = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  let u : spanCommutator d L := ⟨x, hx.1⟩
  have hz : h.coordinates u = 1 := by
    apply Multiplicative.toAdd.injective
    change (h.coordinates u).toAdd = 0
    funext i
    apply natural_fixed_eq_zero (by simp [Space])
    intro g
    obtain ⟨l, hl⟩ := linearAction_surjective (by decide) h.model g
    rw [← hl, ← h.equivariant, action_fixed u hx.2 l]
  have hu : u = 1 := h.coordinates.injective (hz.trans h.coordinates.map_one.symm)
  exact congrArg Subtype.val hu

/-- Natural and dual fixed vectors vanish separately, using the inverse
in the contragredient action rather than identifying the two modules. -/
theorem NaturalDual.centralizer_eq_bot (h : NaturalDual d L) :
    spanCommutator d L ⊓ centralizer (L : Set G) = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  let u : spanCommutator d L := ⟨x, hx.1⟩
  have hz : h.coordinates u = 1 := by
    apply Multiplicative.toAdd.injective
    change (h.coordinates u).toAdd = 0
    apply Prod.ext
    · apply natural_fixed_eq_zero (by simp [Space])
      intro g
      obtain ⟨l, hl⟩ := linearAction_surjective (by decide) h.model g
      have he := congrArg Prod.fst (h.equivariant l u)
      rw [action_fixed u hx.2 l, BinaryLinear.NaturalDualFlag.action_fst, hl] at he
      exact he.symm
    · apply dual_fixed_eq_zero (by simp [Space])
      intro g v
      obtain ⟨l, hl⟩ := linearAction_surjective (by decide) h.model g.symm
      have he := congrArg (fun w => w.2 v) (h.equivariant l u)
      rw [action_fixed u hx.2 l, BinaryLinear.NaturalDualFlag.action_snd, hl,
        LinearEquiv.symm_symm] at he
      exact he.symm
  have hu : u = 1 := h.coordinates.injective (hz.trans h.coordinates.map_one.symm)
  exact congrArg Subtype.val hu

/-- Both alternatives kill precisely the centralizer in `U_L`.
The centralizer in `W_L` is not removed by this theorem. -/
theorem ModuleAlternatives.centralizer_eq_bot (h : ModuleAlternatives d L) :
    spanCommutator d L ⊓ centralizer (L : Set G) = ⊥ := by
  rcases h with h | h
  · obtain ⟨r, _, _, hr⟩ := h
    exact hr.elim fun k => k.centralizer_eq_bot
  · exact h.elim fun k => k.centralizer_eq_bot

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive

end
