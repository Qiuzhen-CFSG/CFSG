module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Action

/-!
# Linear moved spaces and the ambient commutator supports

The binary commutator span maps to the literal group commutator under the
original inclusion U_v → G. Applying the same identity a second time gives
exactly [[U_v,H],H_i]. Thus a linear rank-two conclusion means order four
for the specified factor support, with no change of action or quotient.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.6 and the first decomposition in 13.6.13, printed pp.105 and 929.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction
variable {G : Type*} [Group G] (z v : G) [IsElementaryAbelian 2 (Uv z v)]

def ambientSpace (W : Submodule (ZMod 2) (Additive (Uv z v))) : Subgroup G :=
  W.toAddSubgroup.toSubgroup'.map (Uv z v).subtype

private def subgroupSpace (B : Subgroup G) : Submodule (ZMod 2) (Additive (Uv z v)) :=
  AddSubgroup.toZModSubmodule (n := 2) ((B.comap (Uv z v).subtype).toAddSubgroup)

theorem mem_ambientSpace (W : Submodule (ZMod 2) (Additive (Uv z v))) (w : Uv z v) :
    (w : G) ∈ ambientSpace z v W ↔ Additive.ofMul w ∈ W :=
  mem_map_iff_mem (Uv z v).subtype_injective

theorem ambientSpace_top : ambientSpace z v ⊤ = Uv z v := by
  change (⊤ : Subgroup (Uv z v)).map (Uv z v).subtype = _
  rw [← MonoidHom.range_eq_map, range_subtype]

theorem ambientSpace_commutator
    (W : Submodule (ZMod 2) (Additive (Uv z v))) (A : Subgroup (Gstar z v)) :
    ambientSpace z v (subspaceCommutator (starRepresentation z v) W A) =
      ⁅ambientSpace z v W, starPreimage z v A⁆ := by
  let C := ⁅ambientSpace z v W, starPreimage z v A⁆
  have hspan : subspaceCommutator (starRepresentation z v) W A ≤ subgroupSpace z v C := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, w, hw, rfl⟩
    obtain ⟨g, rfl⟩ := starMk_surjective z v a
    change (((starRepresentation z v (starMk z v g) w).toMul : Uv z v) : G) /
      (w.toMul : G) ∈ C
    rw [starRepresentation_mk_apply, div_eq_mul_inv]
    have hg : (g : G) ∈ starPreimage z v A := ⟨g, ha, rfl⟩
    have hu : (w.toMul : G) ∈ ambientSpace z v W :=
      (mem_ambientSpace z v W w.toMul).mpr hw
    exact (commutator_comm _ _).le (commutator_mem_commutator hg hu)
  apply le_antisymm
  · rintro _ ⟨w, hw, rfl⟩
    exact hspan hw
  · rw [commutator_comm]
    apply commutator_le.mpr
    rintro g ⟨a, ha, rfl⟩ u ⟨w, hw, rfl⟩
    let d := starRepresentation z v (starMk z v a) (Additive.ofMul w) - Additive.ofMul w
    refine ⟨d.toMul, ?_, ?_⟩
    · change d ∈ subspaceCommutator (starRepresentation z v) W A
      exact Submodule.subset_span ⟨starMk z v a, ha, Additive.ofMul w, hw, rfl⟩
    · change ((starRepresentation z v (starMk z v a) (Additive.ofMul w)).toMul : G) /
        (w : G) = _
      rw [starRepresentation_mk_apply, div_eq_mul_inv]
      rfl

theorem ambientSpace_card (W : Submodule (ZMod 2) (Additive (Uv z v))) :
    Nat.card (ambientSpace z v W) = Nat.card W := by
  rw [ambientSpace, card_map_of_injective (Uv z v).subtype_injective]
  exact Nat.card_congr (Equiv.refl _)

theorem moved_ambientSpace (A : Subgroup (Gstar z v)) :
    ambientSpace z v (subspaceCommutator (starRepresentation z v) ⊤ A) =
      movedSubgroup z v A := by
  rw [ambientSpace_commutator, ambientSpace_top]
  rfl

theorem support_ambientSpace (H A : Subgroup (Gstar z v)) :
    ambientSpace z v (subspaceCommutator (starRepresentation z v)
      (subspaceCommutator (starRepresentation z v) ⊤ H) A) = factorSupport z v H A := by
  rw [ambientSpace_commutator, moved_ambientSpace]
  rfl

theorem factorSupport_card_four [Finite G] (H A : Subgroup (Gstar z v))
    (h : Module.finrank (ZMod 2) (subspaceCommutator (starRepresentation z v)
      (subspaceCommutator (starRepresentation z v) ⊤ H) A) = 2) :
    Nat.card (factorSupport z v H A) = 4 := by
  rw [← support_ambientSpace, ambientSpace_card,
    Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, h]
  rfl

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction
end
