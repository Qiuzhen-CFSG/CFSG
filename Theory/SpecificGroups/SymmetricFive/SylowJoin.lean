module
public import Theory.SpecificGroups.SymmetricFive.SylowOvergroup

/-!
# Proper Sylow overgroups cannot generate the symmetric group on five points

A proper Sylow two-overgroup fixes a point. Two distinct fixed points
would put the Sylow subgroup of order eight inside a two-point stabilizer
of order six. Thus both overgroups fix the same point and their join is
proper. The only finite certificate counts these two-point stabilizers.

Source application: the A₅ component exclusion in Aschbacher–Smith
13.4.7, printed p.900.
-/

public noncomputable section
open Subgroup
namespace Theory.SpecificGroups.SymmetricFive.SylowOvergroup

private theorem five_pair_stabilizer_card (i j : Fin 5) (hij : i ≠ j) :
    Nat.card (MulAction.stabilizer (Equiv.Perm (Fin 5)) i ⊓
      MulAction.stabilizer (Equiv.Perm (Fin 5)) j : Subgroup (Equiv.Perm (Fin 5))) = 6 := by
  let : DecidablePred (· ∈ (MulAction.stabilizer (Equiv.Perm (Fin 5)) i ⊓
      MulAction.stabilizer (Equiv.Perm (Fin 5)) j : Subgroup (Equiv.Perm (Fin 5)))) :=
    fun g => inferInstanceAs (Decidable (g i = i ∧ g j = j))
  rw [Nat.card_eq_fintype_card]
  revert i j hij
  decide +kernel

/-- Proper subgroups containing a common Sylow two-subgroup of S₅ do not generate S₅. -/
theorem proper_sylow_overgroups_join_ne_top
    (S : Sylow 2 (Equiv.Perm (Fin 5)))
    (A B : Subgroup (Equiv.Perm (Fin 5)))
    (hA : A ≠ ⊤) (hB : B ≠ ⊤)
    (hSA : (S : Subgroup _) ≤ A) (hSB : (S : Subgroup _) ≤ B) : A ⊔ B ≠ ⊤ := by
  obtain ⟨i,hi⟩ := Theory.SpecificGroups.SymmetricFive.SylowOvergroup.exists_le_point_stabilizer S A hSA hA
  obtain ⟨j,hj⟩ := Theory.SpecificGroups.SymmetricFive.SylowOvergroup.exists_le_point_stabilizer S B hSB hB
  have he : i = j := by
    by_contra hne
    have hc := card_dvd_of_le (le_inf (hSA.trans hi) (hSB.trans hj))
    have hS : Nat.card S = 8 := by
      rw [S.card_eq_multiplicity]
      norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
      decide +kernel
    rw [hS,five_pair_stabilizer_card i j hne] at hc
    norm_num at hc
  subst j
  intro hh
  have hall : (⊤ : Subgroup (Equiv.Perm (Fin 5))) ≤ MulAction.stabilizer _ i :=
    hh ▸ sup_le hi hj
  have hindex := congrArg Subgroup.index (top_unique hall)
  rw [MulAction.index_stabilizer, MulAction.orbit_eq_univ] at hindex
  simp at hindex

end Theory.SpecificGroups.SymmetricFive.SylowOvergroup
