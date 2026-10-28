module

public import Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition.Canonical

/-!
# Concrete residual actions on seven letters

The two tetrahedral actions on six letters extend by a fixed seventh point.
Their two-cores are the images of the literal Klein four subgroup of A₄.
The third model is a three-cycle on `{4,5,6}`. Named double transpositions in
the first two cores support coordinate fixed-space bounds; the third action
has displacement supported on only three coordinates.

These are concrete action models for the local calculation in the final
proof of Aschbacher–Smith 15.3.1, printed p.1155 (combined manuscript of
1 March 2004). Recognition of arbitrary index-three Sylow overgroups in S₇
is separate from their definition and the core calculations here.
-/

@[expose] public section

open Subgroup Equiv
open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition
namespace Theory.SpecificGroups.SymmetricSeven.LocalResidualModels
abbrev S7 := Equiv.Perm (Fin 7)

/-- Extension by the fixed seventh point. -/
def liftSix : S6 →* S7 :=
  (Equiv.permCongrHom (finSumFinEquiv : Fin 6 ⊕ Fin 1 ≃ Fin 7)).toMonoidHom.comp
    ((Equiv.Perm.sumCongrHom _ _).comp ((MonoidHom.id S6).prod (1 : S6 →* Equiv.Perm (Fin 1))))

theorem liftSix_injective : Function.Injective liftSix := by
  intro x y h
  have hh := Equiv.Perm.sumCongrHom_injective ((Equiv.permCongrHom _).injective h)
  exact congrArg Prod.fst hh

def duadResidual7 : Subgroup S7 := duadHom.range.map liftSix
def synthemeResidual7 : Subgroup S7 := synthemeHom.range.map liftSix
def cubic7 : S7 := Equiv.swap 4 5 * Equiv.swap 5 6
def cubicResidual7 : Subgroup S7 := zpowers cubic7

def common7 : S7 := Equiv.swap 2 3 * Equiv.swap 4 5
def duadOther7 : S7 := Equiv.swap 2 4 * Equiv.swap 3 5
def synthemeOther7 : S7 := Equiv.swap 0 1 * Equiv.swap 2 3

private theorem core_range7 (f : A →* S7) (hf : Function.Injective f) :
    f.range.pCoreIn 2 = klein.map f := by
  rw [pCoreIn, ← pCore_map_iso 2 (MonoidHom.ofInjective hf), map_map, klein_core]
  rfl

theorem duadResidual7_core : duadResidual7.pCoreIn 2 = klein.map (liftSix.comp duadHom) := by
  rw [duadResidual7, ← MonoidHom.range_comp]
  exact core_range7 _ (liftSix_injective.comp duadHom_injective)

theorem synthemeResidual7_core : synthemeResidual7.pCoreIn 2 = klein.map (liftSix.comp synthemeHom) := by
  rw [synthemeResidual7, ← MonoidHom.range_comp]
  exact core_range7 _ (liftSix_injective.comp synthemeHom_injective)

private def double01 : A := ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by decide⟩
private def double02 : A := ⟨Equiv.swap 0 2 * Equiv.swap 1 3, by decide⟩
private def double03 : A := ⟨Equiv.swap 0 3 * Equiv.swap 1 2, by decide⟩

theorem common7_mem_duad_core : common7 ∈ duadResidual7.pCoreIn 2 := by
  rw [duadResidual7_core]
  exact ⟨double01, by change double01 ^ 2 = 1; decide, by decide⟩

theorem duadOther7_mem_core : duadOther7 ∈ duadResidual7.pCoreIn 2 := by
  rw [duadResidual7_core]
  exact ⟨double02, by change double02 ^ 2 = 1; decide, by decide⟩

theorem common7_mem_syntheme_core : common7 ∈ synthemeResidual7.pCoreIn 2 := by
  rw [synthemeResidual7_core]
  exact ⟨double01, by change double01 ^ 2 = 1; decide, by decide⟩

theorem synthemeOther7_mem_core : synthemeOther7 ∈ synthemeResidual7.pCoreIn 2 := by
  rw [synthemeResidual7_core]
  exact ⟨double03, by change double03 ^ 2 = 1; decide, by decide⟩

theorem cubicResidual7_card : Nat.card cubicResidual7 = 3 := by
  rw [cubicResidual7, Nat.card_zpowers]
  exact orderOf_eq_prime (by decide : cubic7 ^ 3 = 1) (by decide : cubic7 ≠ 1)

theorem cubicResidual7_core : cubicResidual7.pCoreIn 2 = ⊥ := by
  apply Subgroup.card_eq_one.mp
  rcases (isPGroup_pCoreIn 2 cubicResidual7).card_eq_or_dvd with h | h
  · exact h
  · have hd := h.trans (Subgroup.card_dvd_of_le (pCoreIn_le 2 cubicResidual7))
    rw [cubicResidual7_card] at hd
    norm_num at hd

end Theory.SpecificGroups.SymmetricSeven.LocalResidualModels
