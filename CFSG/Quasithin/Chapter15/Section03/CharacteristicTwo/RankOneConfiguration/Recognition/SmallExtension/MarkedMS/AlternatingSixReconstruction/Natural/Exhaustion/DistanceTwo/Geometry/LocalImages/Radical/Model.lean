module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.LocalImages.Orders
/-!
# A central transposition isolates the full Sylow obstruction

An abelian sign kernel together with a central odd involution generates an
abelian subgroup. In a binary subgroup of S₆ of order at most eight that
kernel has order at most four. Thus a nonabelian binary subgroup containing
a central transposition has order sixteen. No subgroup enumeration is needed.
The literal replacement application is in Radical.Source.
Source context: MS93 (3.3)(ii), (3.6), printed pp.866--871.
-/

open Subgroup
open scoped IsMulCommutative
public noncomputable section
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.LocalImages
private theorem commutative_small (C : Subgroup (Equiv.Perm (Fin 6)))
    (hp : IsPGroup 2 C) (hc : Nat.card C < 8) : IsMulCommutative C := by
  obtain ⟨n,hn⟩ := hp.exists_card_eq
  have hn3 : n < 3 := by
    apply (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
    change 2^n < 8
    omega
  by_cases h2 : n = 2
  · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by simpa [h2] using hn)
  · let : IsCyclic C := isCyclic_of_card_dvd_prime (p := 2) (by
      rw [hn]
      have hcases : n = 0 ∨ n = 1 := by omega
      rcases hcases with rfl | rfl <;> norm_num)
    infer_instance

private theorem commutative_of_central_swap (B : Subgroup (Equiv.Perm (Fin 6)))
    (hp : IsPGroup 2 B) (hcard : Nat.card B ≤ 8)
    (t : Equiv.Perm (Fin 6)) (ht : t.IsSwap) (htB : t ∈ B)
    (hcent : ∀ b ∈ B, t*b=b*t) : IsMulCommutative B := by
  let C := B ⊓ alternatingGroup (Fin 6)
  have hCB : C ≤ B := inf_le_left
  have hCne : C ≠ B := by
    intro he
    have hh : t ∈ alternatingGroup (Fin 6) := (he.symm ▸ htB : t ∈ C).2
    have hh' := Equiv.Perm.mem_alternatingGroup.mp hh
    rw [ht.sign_eq] at hh'
    cases hh'
  have hlt : Nat.card C < Nat.card B := by
    have hle := card_le_of_le hCB
    have hne : Nat.card C ≠ Nat.card B := fun he => hCne (eq_of_le_of_card_ge hCB he.ge)
    omega
  let := commutative_small C (hp.of_injective (inclusion hCB) (inclusion_injective _))
    (lt_of_lt_of_le hlt hcard)
  have hCC : C ≤ centralizer (C : Set (Equiv.Perm (Fin 6))) :=
    commutator_eq_bot_iff_le_centralizer.mp (commutator_self_eq_bot_iff.mpr inferInstance)
  have hCen : C ≤ centralizer (zpowers t : Set (Equiv.Perm (Fin 6))) := by
    apply le_centralizer_iff.mp
    exact zpowers_le.mpr (fun c hc => (hcent c (hCB hc)).symm)
  have hdecomp : B = C ⊔ zpowers t := by
    apply le_antisymm
    · intro b hb
      by_cases he : Equiv.Perm.sign b = 1
      · exact mem_sup_left ⟨hb, Equiv.Perm.mem_alternatingGroup.mpr he⟩
      · have hm : Equiv.Perm.sign b = -1 := by
          rcases Int.units_eq_one_or (Equiv.Perm.sign b) with hh | hh
          · exact (he hh).elim
          · exact hh
        have hbt : b*t ∈ C := ⟨B.mul_mem hb htB, Equiv.Perm.mem_alternatingGroup.mpr (by
          rw [map_mul,hm,ht.sign_eq]; decide)⟩
        have hmem := (C ⊔ zpowers t).mul_mem (mem_sup_left hbt) (mem_sup_right (mem_zpowers t))
        have ht2 : t*t=1 := by rw [←pow_two,←ht.orderOf,pow_orderOf_eq_one]
        simpa only [mul_assoc,ht2,mul_one] using hmem
    · exact sup_le hCB (zpowers_le.mpr htB)
  have hct : C ≤ centralizer (B : Set (Equiv.Perm (Fin 6))) := by
    apply le_centralizer_iff.mp
    rw [hdecomp]
    exact sup_le (le_centralizer_iff.mp hCC) (le_centralizer_iff.mp hCen)
  have htC : zpowers t ≤ centralizer (B : Set (Equiv.Perm (Fin 6))) :=
    zpowers_le.mpr (fun b hb => (hcent b hb).symm)
  apply commutator_self_eq_bot_iff.mp
  apply commutator_eq_bot_iff_le_centralizer.mpr
  exact hdecomp.le.trans (sup_le hct htC)
/-- A binary image with a central transposition is abelian unless it fills
an entire Sylow subgroup of S₆. The sign kernel splits off the transposition;
a proper image has even part of order at most four. -/
theorem commutative_or_card_sixteen_of_central_swap
    (B : Subgroup (Equiv.Perm (Fin 6))) (hp : IsPGroup 2 B)
    (t : Equiv.Perm (Fin 6)) (ht : t.IsSwap) (htB : t ∈ B)
    (hcent : ∀ b ∈ B, t*b=b*t) : IsMulCommutative B ∨ Nat.card B = 16 := by
  by_cases h16 : Nat.card B = 16
  · exact Or.inr h16
  obtain ⟨P,hBP⟩ := hp.exists_le_sylow
  have hPc : Nat.card (P : Subgroup (Equiv.Perm (Fin 6))) = 16 := by
    rw [P.card_eq_multiplicity,Nat.card_perm,Nat.card_fin]
    decide +kernel
  have hB16 := (card_le_of_le hBP).trans_eq hPc
  obtain ⟨n,hn⟩ := hp.exists_card_eq
  have hn4 : n < 4 := by
    apply (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
    change 2^n < 16
    omega
  have h8 : Nat.card B ≤ 8 := by
    rw [hn]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : n ≤ 3)
  exact Or.inl (commutative_of_central_swap B hp h8 t ht htB hcent)
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.LocalImages
