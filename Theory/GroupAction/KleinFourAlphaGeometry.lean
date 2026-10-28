module
public import Theory.GroupTheory.SpecificGroups.KleinFourFullAction
public import Theory.GroupTheory.CardFourAutomorphismStabilizer
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.Data.Fintype.Perm

/-!
# Fixed spaces and two conjugates on a four-group

An involution subgroup of Aut(E₄) fixes two points; a cubic subgroup fixes
only the identity.  Every two-subgroup has order at most two, and two
cubic-conjugate involution subgroups generate the full automorphism group.
These are the one-plane calculations in Aschbacher--Smith B.6.10 and the
literal B.2.18 application used there (printed pp.81 and117).
-/

@[expose] public section
open Subgroup
namespace IsKleinFour
variable {W : Type*} [Group W] [Finite W] [IsKleinFour W]

theorem two_subgroup_card_dvd_two (B : Subgroup (MulAut W)) (hB : IsPGroup 2 B) :
    Nat.card B ∣ 2 := by
  have hd : Nat.card B ∣ 6 := (card_mulAut W) ▸ B.card_subgroup_dvd_card
  have hc : Nat.Coprime (Nat.card B) 3 := by
    obtain ⟨n,hn⟩ := hB.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 3).pow_left n
  exact hc.dvd_mul_right.mp hd

theorem two_fixed_card (B : Subgroup (MulAut W)) (hB : Nat.card B = 2) :
    Nat.card (FixedPoints.subgroup B W) = 2 := by
  let F := FixedPoints.subgroup B W
  have hp : IsPGroup 2 B := IsPGroup.of_card (n := 1) (by simpa using hB)
  have hm := hp.card_modEq_card_fixedPoints W
  change Nat.card W % 2 = Nat.card F % 2 at hm
  rw [card_four] at hm
  have hpos : 0 < Nat.card F := Nat.card_pos
  have hle : Nat.card F ≤ 4 := (F.card_le_card_group).trans_eq card_four
  have hne : Nat.card F ≠ 4 := by
    intro h
    have htop : F = ⊤ := F.eq_top_of_card_eq (h.trans card_four.symm)
    have hb : B = ⊥ := by
      apply le_antisymm _ bot_le
      intro b hb
      apply MulEquiv.ext
      intro w
      have hw : w ∈ F := htop.symm ▸ mem_top w
      exact (FixedPoints.mem_subgroup (M := B) (α := W) (a := w)).mp hw ⟨b,hb⟩
    rw [hb,card_bot] at hB
    omega
  change Nat.card F = 2
  omega

theorem three_fixed_card (C : Subgroup (MulAut W)) (hC : Nat.card C = 3) :
    Nat.card (FixedPoints.subgroup C W) = 1 := by
  have hb : FixedPoints.subgroup C W = ⊥ := by
    apply le_antisymm _ bot_le
    intro w hw
    by_contra hn
    have hle := card_mulAut_subgroup_le_two_of_fixed_point
      (card_four (G := W)) w hn C (fun c hc =>
        (FixedPoints.mem_subgroup (M := C) (α := W) (a := w)).mp hw ⟨c,hc⟩)
    omega
  rw [hb,card_bot]

theorem two_subgroup_rank_le_fixed_codim
    (B : Subgroup (MulAut W)) (hB : IsPGroup 2 B) :
    Nat.log 2 (Nat.card B) ≤ 2 - Nat.log 2 (Nat.card (FixedPoints.subgroup B W)) := by
  rcases (Nat.dvd_prime Nat.prime_two).mp (two_subgroup_card_dvd_two B hB) with h | h
  · rw [h]; simp
  · rw [two_fixed_card B h,h]; decide

set_option synthInstance.maxSize 1000 in
private theorem perm_three_words : ∀ a c p : Equiv.Perm (Fin 3),
    a^2=1 → a≠1 → c^3=1 → c≠1 →
    p=1 ∨ p=a ∨ p=c*a*c⁻¹ ∨ p=a*(c*a*c⁻¹) ∨
      p=(c*a*c⁻¹)*a ∨ p=a*(c*a*c⁻¹)*a := by decide +kernel

omit [Finite W] in
theorem two_three_two_conjugates (B C : Subgroup (MulAut W))
    (hB : Nat.card B = 2) (hC : Nat.card C = 3) :
    ∃ c ∈ C, B ⊔ B.map (MulAut.conj c).toMonoidHom = ⊤ := by
  have hBn : B ≠ ⊥ := fun h => by rw [h,card_bot] at hB; omega
  have hCn : C ≠ ⊥ := fun h => by rw [h,card_bot] at hC; omega
  obtain ⟨⟨a,ha⟩,han⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBn
  obtain ⟨⟨c,hc⟩,hcn⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hCn
  have ha1 : a ≠ 1 := fun h => han (Subtype.ext h)
  have hc1 : c ≠ 1 := fun h => hcn (Subtype.ext h)
  have ha2 : a^2=1 := by
    have h : (⟨a,ha⟩ : B)^Nat.card B=1 := pow_card_eq_one'
    rw [hB] at h
    exact congrArg Subtype.val h
  have hc3 : c^3=1 := by
    have h : (⟨c,hc⟩ : C)^Nat.card C=1 := pow_card_eq_one'
    rw [hC] at h
    exact congrArg Subtype.val h
  let e := autEquivPermThree W
  let D := B ⊔ B.map (MulAut.conj c).toMonoidHom
  have ham : a ∈ D := (le_sup_left : B ≤ D) ha
  have hcm : c*a*c⁻¹ ∈ D :=
    (le_sup_right : B.map (MulAut.conj c).toMonoidHom ≤ D) ⟨a,ha,rfl⟩
  refine ⟨c,hc,top_unique ?_⟩
  intro p _
  have hp := perm_three_words (e a) (e c) (e p)
    (by rw [←map_pow,ha2,map_one]) (by simpa using ha1)
    (by rw [←map_pow,hc3,map_one]) (by simpa using hc1)
  have hp' : p=1 ∨ p=a ∨ p=c*a*c⁻¹ ∨ p=a*(c*a*c⁻¹) ∨
      p=(c*a*c⁻¹)*a ∨ p=a*(c*a*c⁻¹)*a := by
    simpa only [←map_one e,←map_mul,←map_inv,e.injective.eq_iff] using hp
  rcases hp' with rfl|rfl|rfl|rfl|rfl|rfl
  · exact D.one_mem
  · exact ham
  · exact hcm
  · exact D.mul_mem ham hcm
  · exact D.mul_mem hcm ham
  · exact D.mul_mem (D.mul_mem ham hcm) ham

end IsKleinFour
