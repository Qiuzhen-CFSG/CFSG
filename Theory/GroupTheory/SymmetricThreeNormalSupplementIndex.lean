module

public import Theory.GroupTheory.CyclicHallNormalizerEscape
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Data.Fintype.Perm

/-!
# Index three from a normal symmetric-three supplement

Suppose I is normal, I/O₂(I) is S₃, and I together with a proper Sylow
two-overgroup M generates G. The normal-product order formula makes [G:M]
divide |I|. It is odd since M contains a Sylow two-subgroup, so it divides
three and must equal three.

This supplies the index step in Aschbacher–Smith 13.4.8, printed p.905.
The displayed source equality |I:O₂(I)|=3 cannot be literal: its clause (2)
identifies that quotient with S₃, of order six. The required conclusion
[G:M]=3 follows instead from the common Sylow subgroup as proved here.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

theorem index_three_of_symmetricThree_normal_supplement
    (I M : Subgroup G) [I.Normal]
    (e : (I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 3))
    (P : Sylow 2 G) (hPM : (P : Subgroup G) ≤ M)
    (hM : M ≠ ⊤) (hgen : I ⊔ M = ⊤) : M.index = 3 := by
  have hd : M.index ∣ Nat.card I := index_dvd_of_normal_supplement I M hgen
  have hodd : ¬ 2 ∣ M.index := fun h => P.not_dvd_index (h.trans (index_dvd_of_le hPM))
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := I)).exists_card_eq
  have hquot : Nat.card (I ⧸ pCore 2 I) = 6 := by
    rw [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]
    decide
  have hcard : Nat.card I = 2 ^ (n+1) * 3 := by
    have hh := (pCore 2 I).card_mul_index
    change Nat.card (pCore 2 I) * Nat.card (I ⧸ pCore 2 I) = Nat.card I at hh
    rw [hn,hquot] at hh
    rw [← hh,pow_succ]
    ring
  rw [hcard] at hd
  have hcop : Nat.Coprime M.index (2 ^ (n+1)) :=
    (Nat.prime_two.coprime_iff_not_dvd.mpr hodd).symm.pow_right _
  have hd3 : M.index ∣ 3 := hcop.dvd_mul_left.mp hd
  exact ((Nat.dvd_prime Nat.prime_three).mp hd3).resolve_left
    (fun he => hM (index_eq_one.mp he))

end Theory.GroupTheory
