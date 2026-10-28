module

public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.Center
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Rank and relative index at the central root plane

Each coordinate root has relative index |F| in the actual Sylow center.
A nontrivial elementary subgroup of rank at least 2n fills that center.
The strict F−1 inequality passes to conjugate subgroups and to subgroups
of the genuine commutator group whose images lie in this center. No root
membership in the binary derived group is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.7,
printed p.389, the central-subgroup cases of the a and α arguments.
-/

public section

open Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open Representation.OneCohomology.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph
namespace SymplecticConjugatePair
variable {F : Type*} [Field F] [CharP F 2] [Finite F] [Algebra (ZMod 2) F]
set_option linter.unusedSectionVars false

lemma central_eq_of_rank_ge {n : ℕ} (hF : Nat.card F = 2^n)
    {B : Subgroup (Sp F)} (hB : B ≤ sylowCenter) (hbe : IsElementaryTwo B)
    (hr : 2*n ≤ rank B) : B = sylowCenter := by
  apply Subgroup.eq_of_le_of_card_ge hB
  rw [card_sylowCenter,hF,← pow_mul,hbe.card_eq_two_pow_rank]
  apply Nat.pow_le_pow_right (by decide : 0 < 2)
  omega

lemma root_relIndex_sylowCenter (r : Fin 8) (hr : r = 0 ∨ r = 4) :
    (RootSubgroup.group (F := F) r).relIndex sylowCenter = Nat.card F := by
  have hle : RootSubgroup.group (F := F) r ≤ sylowCenter := by
    rcases hr with rfl | rfl
    · exact root_zero_le_sylowCenter
    · exact root_four_le_sylowCenter
  have h := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup (Sp F))
    (RootSubgroup.group r) sylowCenter bot_le hle
  simp only [Subgroup.relIndex_bot_left,RootSubgroup.card,card_sylowCenter,pow_two] at h
  exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := F)) h

lemma root_log_relIndex_sylowCenter {n : ℕ} (hF : Nat.card F = 2^n)
    (r : Fin 8) (hr : r = 0 ∨ r = 4) :
    Nat.log 2 ((RootSubgroup.group (F := F) r).relIndex sylowCenter) = n := by
  rw [root_relIndex_sylowCenter r hr,hF,Nat.log_pow (by decide : 1 < 2)]

lemma root_group_ne_bot (r : Fin 8) : RootSubgroup.group (F := F) r ≠ ⊥ := by
  intro h
  have hm : rootElement r (1:F) ∈ RootSubgroup.group r :=
    (RootSubgroup.mem_group_iff r _).mpr ⟨1,rfl⟩
  rw [h,Subgroup.mem_bot] at hm
  have ho := root_involution r (one_ne_zero : (1:F) ≠ 0)
  simp [hm] at ho

lemma derived_central_subgroup_not_offender {n : ℕ} (hF : Nat.card F = 2^n)
    (hn : 0 < n) {B : Subgroup (commutator (Sp F))}
    (hB : B.map (commutator (Sp F)).subtype ≤ sylowCenter) (hne : B ≠ ⊥) :
    rank B + 1 < fixedCodim (derivedPair (graphAut (F := F))) B := by
  have hmap : B.map (commutator (Sp F)).subtype ≠ ⊥ := by
    intro h
    exact hne ((Subgroup.map_eq_bot_iff_of_injective B
      (commutator (Sp F)).subtype_injective).mp h)
  have h := central_subgroup_not_offender hF hn hB hmap
  rw [rank_map_injective _ Subtype.val_injective] at h
  change rank B + 1 < Module.finrank (ZMod 2)
    (Space F ⧸ fixedSpace (graphPair.comp (commutator (Sp F)).subtype) B)
  rw [fixedSpace_comp_map]
  exact h

lemma conjugate_central_subgroup_not_offender {n : ℕ} (hF : Nat.card F = 2^n)
    (hn : 0 < n) {B : Subgroup (Sp F)} (g : Sp F)
    (hB : B.map (MulAut.conj g).toMonoidHom ≤ sylowCenter) (hne : B ≠ ⊥) :
    rank B + 1 < fixedCodim (graphPair (F := F)) B := by
  have hmap : B.map (MulAut.conj g).toMonoidHom ≠ ⊥ := by
    intro h
    exact hne ((Subgroup.map_eq_bot_iff_of_injective B (MulAut.conj g).injective).mp h)
  have h := central_subgroup_not_offender hF hn hB hmap
  rwa [rank_map_conj,fixedCodim_map_conj] at h
end SymplecticConjugatePair
