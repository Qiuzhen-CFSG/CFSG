module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Faithfulness of a prime-order Sylow action

If a nonnormal Sylow subgroup has prime order and is self-centralizing,
the conjugation action on Sylow subgroups is faithful. Its kernel lies in
the Sylow normalizer. A nontrivial intersection with the Sylow subgroup
would contain that subgroup, and the Frattini argument would force the
normalizer to be the whole group. The trivial intersection forces the
kernel to centralize the Sylow subgroup and hence to vanish.

This is the kernel argument used in Wong (1964), Theorem 6(a), p.108,
DOI 10.1017/S1446788700022771.
-/

namespace Sylow

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- The action on the Sylow subgroups is faithful when a nonnormal Sylow
subgroup has prime order and is self-centralizing. -/
public theorem toPermHom_injective_of_prime_card_self_centralizing (P : Sylow p G)
    (hP : Nat.card P = p)
    (hcent : Subgroup.centralizer (P : Set G) ≤ (P : Subgroup G))
    (hnorm : Subgroup.normalizer (P : Set G) ≠ ⊤) :
    Function.Injective (MulAction.toPermHom G (Sylow p G)) := by
  let ρ := MulAction.toPermHom G (Sylow p G)
  let K : Subgroup G := ρ.ker
  have hKN : K ≤ Subgroup.normalizer (P : Set G) := by
    intro k hk
    exact Sylow.smul_eq_iff_mem_normalizer.mp
      (Equiv.congr_fun (MonoidHom.mem_ker.mp hk) P)
  have hKP : K ⊓ (P : Subgroup G) = ⊥ := by
    have hd : Nat.card ↥(K ⊓ (P : Subgroup G)) ∣ p :=
      (Subgroup.card_dvd_of_le (show K ⊓ (P : Subgroup G) ≤ P from inf_le_right)).trans
        hP.dvd
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hd with h | h
    · exact Subgroup.card_eq_one.mp h
    · have heq : K ⊓ (P : Subgroup G) = (P : Subgroup G) :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, hP])
      have hPK : (P : Subgroup G) ≤ K := heq ▸ inf_le_left
      have htop := Sylow.normalizer_sup_eq_top' P hPK
      rw [sup_of_le_left hKN] at htop
      exact (hnorm htop).elim
  have hcomm : ⁅K, (P : Subgroup G)⁆ = ⊥ := by
    apply le_antisymm _ bot_le
    apply le_trans _ hKP.le
    exact le_inf (Subgroup.commutator_le_left K (P : Subgroup G))
      (Subgroup.le_normalizer_iff_commutator_le_right.mp hKN)
  have hle : K ≤ (P : Subgroup G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm).trans hcent
  apply (MonoidHom.ker_eq_bot_iff ρ).mp
  exact le_antisymm ((le_inf le_rfl hle).trans hKP.le) bot_le

end Sylow
