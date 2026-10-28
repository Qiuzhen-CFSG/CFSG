module

public import Theory.GroupTheory.SpecificGroups.KleinFourFixedAut
public import Theory.GroupTheory.SpecificGroups.KleinFourAut
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Index
import Mathlib.Tactic

/-!
# Moving a four-group with a large involution centralizer

A self-centralizing four-group has at most eight normalizer elements fixing
one prescribed nonidentity element: the conjugation kernel has order four,
and the image fixes an element and has order at most two. If a subgroup N
has at most four elements centralizing that involution, it contains at most
one four-group through it. A larger centralizing subgroup therefore supplies
a conjugate outside N.

This is the counting argument for the diagonal branch of Guralnick--Malle,
*Classification of 2F-modules I*, Proposition 4.1, manuscript pp.8--9.
-/

public section
open Subgroup
namespace Theory.PSL2.SmallPrimeFourGroup

/-- The stabilizer of a nonidentity element in the normalizer of a
self-centralizing four-group has order at most eight. -/
theorem normalizer_fixed_card_le_eight {G : Type*} [Group G] [Finite G]
    (A C : Subgroup G) [IsKleinFour A] (b : G) (hb : b ∈ A) (hb1 : b ≠ 1)
    (hC : C ≤ centralizer ({b} : Set G))
    (hCA : C ≤ normalizer (A : Set G))
    (hself : centralizer (A : Set G) = A) : Nat.card C ≤ 8 := by
  let f : C →* MulAut A := A.normalizerMonoidHom.comp (inclusion hCA)
  let bA : A := ⟨b, hb⟩
  have hbA : bA ≠ 1 := fun h => hb1 (congrArg Subtype.val h)
  have hfix : ∀ a ∈ f.range, a bA = bA := by
    rintro a ⟨c, rfl⟩
    apply Subtype.ext
    change (c : G) * b * (c : G)⁻¹ = b
    rw [mem_centralizer_singleton_iff.mp (hC c.property)]
    simp
  have hp := IsKleinFour.isPGroup_aut_subgroup_of_fixed_ne_one f.range hbA hfix
  have hrdiv : Nat.card f.range ∣ 6 := by
    rw [← IsKleinFour.card_mulAut A]
    exact f.range.card_subgroup_dvd_card
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have hr : Nat.card f.range ≤ 2 := by
    have hle := Nat.le_of_dvd (by decide : 0 < 6) hrdiv
    have hnlt : n < 3 := by
      apply (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
      omega
    rw [hn] at hrdiv ⊢
    interval_cases n <;> norm_num at *
  have hk : Nat.card f.ker ≤ 4 := by
    have hkA : ∀ c : f.ker, (c.val : G) ∈ A := by
      intro c
      apply hself.le
      have hc : A.normalizerMonoidHom (inclusion hCA c.val) = 1 := c.property
      rw [← MonoidHom.mem_ker, normalizerMonoidHom_ker] at hc
      exact hc
    let j : f.ker → A := fun c => ⟨c.val, hkA c⟩
    have hj : Function.Injective j := by
      intro c d h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : A => (x : G)) h
    simpa only [IsKleinFour.card_four] using Nat.card_le_card_of_injective j hj
  have hc := f.ker.card_mul_index
  rw [index_ker] at hc
  nlinarith

/-- A large subgroup centralizing a marked involution moves a four-group
out of any subgroup whose centralizer of that involution has order at most four. -/
theorem exists_conjugate_not_le_of_small_centralizer {G : Type*} [Group G] [Finite G]
    (A C N : Subgroup G) [IsKleinFour A] (b : G) (hb : b ∈ A) (hb1 : b ≠ 1)
    (hC : C ≤ centralizer ({b} : Set G)) (hlarge : 8 < Nat.card C)
    (hsmall : Nat.card (N ⊓ centralizer ({b} : Set G) : Subgroup G) ≤ 4)
    (hself : centralizer (A : Set G) = A) :
    ∃ c : G, c ∈ C ∧ ¬ A.map (MulAut.conj c).toMonoidHom ≤ N := by
  classical
  by_contra! hno
  let W := N ⊓ centralizer ({b} : Set G)
  have hAb : A ≤ centralizer ({b} : Set G) := by
    intro a ha
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (IsKleinFour.isMulCommutative.is_comm.comm
      (⟨a, ha⟩ : A) ⟨b, hb⟩)
  have hAW : A ≤ W := by
    refine le_inf ?_ hAb
    intro a ha
    exact hno 1 C.one_mem (mem_map.mpr ⟨a, ha, by simp⟩)
  have hAW_eq : A = W := eq_of_le_of_card_ge hAW (by
    rw [IsKleinFour.card_four (G := A)]
    exact hsmall)
  have hCA : C ≤ normalizer (A : Set G) := by
    intro c hc
    rw [mem_normalizer_iff_map_conj_eq]
    have hcb : c * b * c⁻¹ = b := by
      rw [mem_centralizer_singleton_iff.mp (hC hc)]; simp
    have hcW : A.map (MulAut.conj c).toMonoidHom ≤ W := by
      refine le_inf (hno c hc) ?_
      rintro z ⟨a, ha, rfl⟩
      have hab : Commute a b := mem_centralizer_singleton_iff.mp (hAb ha)
      have hmap := hab.map (MulAut.conj c).toMonoidHom
      change Commute (c * a * c⁻¹) (c * b * c⁻¹) at hmap
      rw [hcb] at hmap
      exact mem_centralizer_singleton_iff.mpr hmap.eq
    have heq : A.map (MulAut.conj c).toMonoidHom = W :=
      eq_of_le_of_card_ge hcW (by
        rw [card_map_of_injective (MulAut.conj c).injective, IsKleinFour.card_four (G := A)]
        exact hsmall)
    exact heq.trans hAW_eq.symm
  have := normalizer_fixed_card_le_eight A C b hb hb1 hC hCA hself
  omega

end Theory.PSL2.SmallPrimeFourGroup
