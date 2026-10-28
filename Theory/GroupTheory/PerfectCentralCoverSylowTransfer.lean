module

public import Theory.GroupTheory.PerfectCentralCover
public import Theory.GroupTheory.Commutator.CentralSylowTransfer
public import Mathlib.Algebra.Ring.Parity

/-!
# Transfer and odd-order lifts for perfect central double covers

The central two-element kernel lies in every Sylow two-subgroup, in its center,
and, by central Sylow transfer, in its derived subgroup. Consequently the Sylow
is the full preimage of its image. If a base element has odd period r, raising
any lift to r+1 gives a lift whose r-th power is one.

These are the generic transfer and lifting steps in the direct proof of the
Sylow-center assertion of GLS4, Chapter 4, Lemma 2.8(c).
-/

namespace PerfectCentralCovering
open Subgroup
variable {E B : Type*} [Group E] [Group B]

public theorem Cover.ker_le_sylow (f : Cover E B)
    (hcard : Nat.card f.toMonoidHom.ker = 2) (P : Sylow 2 E) :
    f.toMonoidHom.ker ≤ P := by
  have hp : IsPGroup 2 f.toMonoidHom.ker :=
    IsPGroup.of_card (n := 1) (by simpa using hcard)
  exact hp.le_sylow_of_normal P

public theorem Cover.ker_le_sylow_commutator [Finite E] (f : Cover E B)
    (hcard : Nat.card f.toMonoidHom.ker = 2) (P : Sylow 2 E) :
    f.toMonoidHom.ker ≤ ⁅(P : Subgroup E), (P : Subgroup E)⁆ := by
  let := f.isPerfect
  intro x hx
  exact center_inf_commutator_inf_sylow_le_commutator P
    ⟨⟨f.ker_le_center hx, Group.IsPerfect.mem_commutator⟩, f.ker_le_sylow hcard P hx⟩

public theorem Cover.comap_map_sylow (f : Cover E B)
    (hcard : Nat.card f.toMonoidHom.ker = 2) (P : Sylow 2 E) :
    ((P : Subgroup E).map f.toMonoidHom).comap f.toMonoidHom = P :=
  comap_map_eq_self (f.ker_le_sylow hcard P)

public theorem Cover.ker_le_sylow_center (f : Cover E B)
    (hcard : Nat.card f.toMonoidHom.ker = 2) (P : Sylow 2 E) :
    f.toMonoidHom.ker ≤ (center P).map (P : Subgroup E).subtype := by
  intro x hx
  refine ⟨⟨x, f.ker_le_sylow hcard P hx⟩, ?_, rfl⟩
  apply mem_center_iff.mpr
  intro y
  exact Subtype.ext (mem_center_iff.mp (f.ker_le_center hx) y)

public theorem Cover.exists_odd_order_lift [Finite E] (f : Cover E B)
    (hcard : Nat.card f.toMonoidHom.ker = 2) (b : B) (r : ℕ)
    (hodd : Odd r) (hb : b ^ r = 1) :
    ∃ t : E, f.toMonoidHom t = b ∧ t ^ r = 1 := by
  obtain ⟨e, he⟩ := f.surjective b
  have hm : e ^ r ∈ f.toMonoidHom.ker := by simp [MonoidHom.mem_ker, he, hb]
  have hsq : (e ^ r) ^ 2 = 1 := by
    have h := pow_card_eq_one' (x := (⟨e ^ r, hm⟩ : f.toMonoidHom.ker))
    rw [hcard] at h
    exact congrArg Subtype.val h
  refine ⟨e ^ (r + 1), ?_, ?_⟩
  · rw [map_pow, he, pow_succ, hb, one_mul]
  · rw [← pow_mul, Nat.mul_comm (r + 1), pow_mul]
    obtain ⟨k, hk⟩ := hodd
    rw [show r + 1 = 2 * (k + 1) by omega, pow_mul, hsq, one_pow]

end PerfectCentralCovering
