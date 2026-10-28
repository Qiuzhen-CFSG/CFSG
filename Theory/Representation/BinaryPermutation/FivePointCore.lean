module
public import Theory.Representation.BinaryPermutation.FiveCentralizerGeometry
public import Mathlib.GroupTheory.PGroup
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Mathlib.Tactic

/-!
The two-core of the stabilizer of a weight-two vector on the binary
five-point core is the transposition on its support. A three-cycle on the
complement forces every other candidate to generate a nontrivial element
of order three. Only the 120 permutations enter the finite inspection.
This is the S3 quotient calculation used in source 5.1.7(1), printed p.633.
-/
public section
namespace BinaryPermutation.FivePointCore
open Subgroup FiveCentralizerGeometry
local instance : DecidablePred (· ∈ core (Fin 5)) := fun x =>
  inferInstanceAs (Decidable ((∑ i, x i) = 0))
local instance : Fintype (core (Fin 5)) := Subtype.fintype _
private def t : Equiv.Perm (Fin 5) := Equiv.swap 0 1
private def c : Equiv.Perm (Fin 5) := Equiv.swap 2 3 * Equiv.swap 3 4
private def w (p : Equiv.Perm (Fin 5)) := p * (c * p * c⁻¹)
private theorem inspection : ∀ p : Equiv.Perm (Fin 5),
    coreRepresentation (Fin 5) p v = v →
      p = 1 ∨ p = t ∨
      ((p^2)^3 = 1 ∧ p^2 ≠ 1) ∨ ((w p)^3 = 1 ∧ w p ≠ 1) := by
  decide +kernel

/-- The original complement cubic detects every extra normal two-element. -/
theorem two_subgroup_le_transposition (P : Subgroup (Equiv.Perm (Fin 5)))
    (hP : IsPGroup 2 P)
    (hfix : ∀ p ∈ P, coreRepresentation (Fin 5) p v = v)
    (hn : Equiv.swap 2 3 * Equiv.swap 3 4 ∈ normalizer (P : Set (Equiv.Perm (Fin 5)))) :
    P ≤ zpowers (Equiv.swap 0 1) := by
  have no_three (a : P) (ha : a^3=1) : a=1 := by
    have hd := orderOf_dvd_of_pow_eq_one ha
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      (hP.orderOf_coprime (by decide : Nat.Coprime 2 3) a) dvd_rfl hd)
  intro p hp
  rcases inspection p (hfix p hp) with rfl | rfl | ⟨ha,hne⟩ | ⟨ha,hne⟩
  · exact one_mem _
  · exact mem_zpowers _
  · exact (hne (congrArg Subtype.val (no_three ⟨p^2,P.pow_mem hp 2⟩ (Subtype.ext ha)))).elim
  · have hw : w p ∈ P := P.mul_mem hp ((mem_normalizer_iff.mp hn p).mp hp)
    exact (hne (congrArg Subtype.val (no_three ⟨w p,hw⟩ (Subtype.ext ha)))).elim

/-- The actual two-core of any five-point stabilizer overgroup lies in its
support transposition. The complement cubic is retained literally. -/
theorem stabilizer_twoCore_le_transposition
    (H : Subgroup (Equiv.Perm (Fin 5)))
    (hfix : ∀ p ∈ H, coreRepresentation (Fin 5) p v = v)
    (hc : Equiv.swap 2 3 * Equiv.swap 3 4 ∈ H) :
    H.pCoreIn 2 ≤ zpowers (Equiv.swap 0 1) := by
  apply two_subgroup_le_transposition _ (isPGroup_pCoreIn 2 H)
    (fun p hp => hfix p (pCoreIn_le 2 H hp))
  exact (H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))) hc

/-- The same bound on the literal image of a normal two-subgroup, as used
for V inside the centralizer of the displacement vector in 5.1.7. -/
theorem normal_two_image_le_transposition {H : Type*} [Group H]
    (q : H →* Equiv.Perm (Fin 5)) (P : Subgroup H) [P.Normal]
    (hP : IsPGroup 2 P)
    (hfix : ∀ g, coreRepresentation (Fin 5) (q g) v = v)
    (hc : Equiv.swap 2 3 * Equiv.swap 3 4 ∈ q.range) :
    P.map q ≤ zpowers (Equiv.swap 0 1) := by
  apply two_subgroup_le_transposition _ (hP.map q)
    (fun p hp => by obtain ⟨g,_,rfl⟩ := hp; exact hfix g)
  obtain ⟨g,hg⟩ := hc
  rw [←hg]
  exact P.le_normalizer_map q ⟨g,le_normalizer_of_normal (mem_top g),rfl⟩

/-- A nonzero displacement of the first support transposition is exactly
its weight-two vector. -/
theorem displacement_swap_zero_one (x : core (Fin 5))
    (hne : coreRepresentation (Fin 5) (Equiv.swap 0 1) x - x ≠ 0) :
    coreRepresentation (Fin 5) (Equiv.swap 0 1) x - x = v := by
  have hs : ∀ y : core (Fin 5),
      coreRepresentation (Fin 5) (Equiv.swap 0 1) y - y = 0 ∨
      coreRepresentation (Fin 5) (Equiv.swap 0 1) y - y = v := by
    decide +kernel
  exact (hs x).resolve_left hne

@[expose] def second : core (Fin 5) := ⟨![0,0,1,1,0], by rw [mem_core]; decide⟩
private def t₂ : Equiv.Perm (Fin 5) := Equiv.swap 2 3
private def c₂ : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 1 4
private def w₂ (p : Equiv.Perm (Fin 5)) := p * (c₂ * p * c₂⁻¹)
private theorem second_inspection : ∀ p : Equiv.Perm (Fin 5),
    coreRepresentation (Fin 5) p second = second →
      p = 1 ∨ p = t₂ ∨
      ((p^2)^3 = 1 ∧ p^2 ≠ 1) ∨ ((w₂ p)^3 = 1 ∧ w₂ p ≠ 1) := by
  decide +kernel

theorem normal_two_second_image_le_transposition {H : Type*} [Group H]
    (q : H →* Equiv.Perm (Fin 5)) (P : Subgroup H) [P.Normal]
    (hP : IsPGroup 2 P)
    (hfix : ∀ g, coreRepresentation (Fin 5) (q g) second = second)
    (hc : Equiv.swap 0 1 * Equiv.swap 1 4 ∈ q.range) :
    P.map q ≤ zpowers (Equiv.swap 2 3) := by
  have no_three (a : P.map q) (ha : a^3=1) : a=1 := by
    have hd := orderOf_dvd_of_pow_eq_one ha
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      ((hP.map q).orderOf_coprime (by decide : Nat.Coprime 2 3) a) dvd_rfl hd)
  obtain ⟨g,hg⟩ := hc
  have hn : c₂ ∈ normalizer (P.map q : Set (Equiv.Perm (Fin 5))) := by
    rw [show c₂ = q g from hg.symm]
    exact P.le_normalizer_map q ⟨g,le_normalizer_of_normal (mem_top g),rfl⟩
  intro p hp
  have hf : coreRepresentation (Fin 5) p second = second := by
    obtain ⟨x,_,rfl⟩ := hp
    exact hfix x
  rcases second_inspection p hf with rfl | rfl | ⟨ha,hne⟩ | ⟨ha,hne⟩
  · exact one_mem _
  · exact mem_zpowers _
  · exact (hne (congrArg Subtype.val (no_three ⟨p^2,(P.map q).pow_mem hp 2⟩ (Subtype.ext ha)))).elim
  · have hw : w₂ p ∈ P.map q := (P.map q).mul_mem hp ((mem_normalizer_iff.mp hn p).mp hp)
    exact (hne (congrArg Subtype.val (no_three ⟨w₂ p,hw⟩ (Subtype.ext ha)))).elim

private def word : Fin 3 → Equiv.Perm (Fin 5) :=
  ![Equiv.swap 0 1,Equiv.swap 2 3,Equiv.swap 0 1 * Equiv.swap 2 3]
private def delta (i : Fin 3) (x : core (Fin 5)) := coreRepresentation (Fin 5) (word i) x - x
private theorem disjoint_inspection : ∀ i j : Fin 3,
    (i=0 ∧ j=1) ∨ (i=1 ∧ j=0) ∨
    ∃ x y : core (Fin 5), delta i x = delta j y ∧ delta i x ≠ 0 := by
  decide +kernel

theorem distinct_supports_of_disjoint_displacements
    (a b : Equiv.Perm (Fin 5))
    (ha : a=Equiv.swap 0 1 ∨ a=Equiv.swap 2 3 ∨ a=Equiv.swap 0 1 * Equiv.swap 2 3)
    (hb : b=Equiv.swap 0 1 ∨ b=Equiv.swap 2 3 ∨ b=Equiv.swap 0 1 * Equiv.swap 2 3)
    (hd : ∀ x y : core (Fin 5),
      coreRepresentation (Fin 5) a x - x = coreRepresentation (Fin 5) b y - y →
      coreRepresentation (Fin 5) a x - x = 0) :
    (a=Equiv.swap 0 1 ∧ b=Equiv.swap 2 3) ∨
      (a=Equiv.swap 2 3 ∧ b=Equiv.swap 0 1) := by
  have hi : ∃ i, word i = a := by
    rcases ha with rfl | rfl | rfl
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
  have hj : ∃ j, word j = b := by
    rcases hb with rfl | rfl | rfl
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
  obtain ⟨i,rfl⟩ := hi
  obtain ⟨j,rfl⟩ := hj
  rcases disjoint_inspection i j with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨x,y,he,hne⟩
  · exact Or.inl ⟨rfl,rfl⟩
  · exact Or.inr ⟨rfl,rfl⟩
  · exact (hne (hd x y he)).elim
end BinaryPermutation.FivePointCore
