module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Sylow
public import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# Normalizer control from a full local automizer

If a subgroup M realizes every automorphism of Y and contains C_G(Y),
then it contains N_G(Y): match the conjugation action of an arbitrary
normalizer element by an element of M and put their quotient in C_G(Y).
The normalizer-index congruence promotes a local Sylow assertion, and a
prime-order Y has a cyclic full automizer of order p-1.

Source application: Aschbacher–Smith, J.2.10, printed p.438 (PDF p.449).
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

/-- A full action realized inside M traps the ambient normalizer once its kernel lies in M. -/
theorem normalizer_le_of_full_action (Y M : Subgroup G)
    (hC : centralizer (Y : Set G) ≤ M)
    (hA : ∀ a : MulAut Y, ∃ n : normalizer (Y : Set G),
      (n : G) ∈ M ∧ Y.normalizerMonoidHom n = a) :
    normalizer (Y : Set G) ≤ M := by
  intro n hn
  obtain ⟨m, hm, he⟩ := hA (Y.normalizerMonoidHom ⟨n, hn⟩)
  have hk : m⁻¹ * ⟨n, hn⟩ ∈ Y.normalizerMonoidHom.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, he, inv_mul_cancel]
  rw [Y.normalizerMonoidHom_ker] at hk
  have hmprod : (m : G) * ((m : G)⁻¹ * n) ∈ M := M.mul_mem hm (hC hk)
  simpa using hmprod

/-- Normalizer control promotes a specified local Sylow subgroup to the ambient group. -/
theorem exists_sylow_of_local_index (Y M : Subgroup G) [Finite G]
    {p : ℕ} [Fact p.Prime] (hY : IsPGroup p Y)
    (hlocal : ¬ p ∣ Y.relIndex M) (hn : normalizer (Y : Set G) ≤ M) :
    ∃ P : Sylow p G, (P : Subgroup G) = Y := by
  have hd : Y.relIndex (normalizer (Y : Set G)) ∣ Y.relIndex M :=
    dvd_of_mul_right_eq _ (relIndex_mul_relIndex Y _ M le_normalizer hn)
  obtain ⟨n, hncard⟩ := hY.exists_card_eq
  have hcongr := Sylow.card_quotient_normalizer_modEq_card_quotient hncard
  have hi : ¬ p ∣ Y.index := by
    intro hi
    exact hlocal (((hcongr.dvd_iff dvd_rfl).mpr hi).trans hd)
  exact ⟨hY.toSylow hi, rfl⟩

/-- The actual conjugation image is cyclic of order p-1 when it is the full automizer. -/
theorem prime_full_automizer (Y : Subgroup G) [Finite Y]
    {p : ℕ} [Fact p.Prime] (hY : Nat.card Y = p)
    (hA : Function.Surjective Y.normalizerMonoidHom) :
    IsCyclic Y.normalizerMonoidHom.range ∧ Nat.card Y.normalizerMonoidHom.range = p - 1 := by
  let : IsCyclic Y := isCyclic_of_prime_card hY
  let : IsCyclic (ZMod (Nat.card Y))ˣ :=
    ZMod.isCyclic_units_prime (hY ▸ Fact.out)
  let : IsCyclic (MulAut Y) := (IsCyclic.mulAutMulEquiv Y).isCyclic.mpr inferInstance
  refine ⟨inferInstance, ?_⟩
  rw [MonoidHom.range_eq_top.mpr hA, Nat.card_congr (topEquiv (G := MulAut Y)).toEquiv,
    IsCyclic.card_mulAut, hY, Nat.totient_prime Fact.out]

end Subgroup
