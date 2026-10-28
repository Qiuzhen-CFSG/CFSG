module

public import Theory.ElementaryAbelian.Basic
public import Theory.SpecificGroups.Alternating.FiveLocalGeometry

/-!
# The rotation plane and reflection four-group in two pentagon groups

The two coordinate reflections normalize the rotation plane of order 25.
Their only invariant subgroups of order five are the two coordinate lines:
conjugating and dividing isolates a nonzero first coordinate, which generates
the line. Only identities in the 100-element product are checked by reduction.

This is the concrete model used by the marked ambient construction for
Aschbacher, *Sporadic Groups* (1994), 47.2, printed p.261.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.SylowAction.SourceFourGroup.Model
abbrev D10 := DihedralGroup 5
abbrev M := D10 × D10

def rotations : Subgroup D10 where
  carrier := {x | ∃ i : ZMod 5, x = .r i}
  one_mem' := ⟨0, rfl⟩
  mul_mem' := by rintro x y ⟨i, rfl⟩ ⟨j, rfl⟩; exact ⟨i+j, rfl⟩
  inv_mem' := by rintro x ⟨i, rfl⟩; exact ⟨-i, rfl⟩

instance : DecidablePred (· ∈ rotations) := fun x => inferInstanceAs (Decidable (∃ i : ZMod 5, x = DihedralGroup.r i))

def reflections : Subgroup D10 where
  carrier := {x | x = 1 ∨ x = .sr 0}
  one_mem' := Or.inl rfl
  mul_mem' := by decide +kernel
  inv_mem' := by decide +kernel

instance : DecidablePred (· ∈ reflections) := fun x => inferInstanceAs (Decidable (x = 1 ∨ x = DihedralGroup.sr (0 : ZMod 5)))

def plane : Subgroup M := rotations.prod rotations
def A : Subgroup M := rotations.prod ⊥
def B : Subgroup M := (⊥ : Subgroup D10).prod rotations
def four : Subgroup M := reflections.prod reflections

instance : DecidablePred (· ∈ plane) := fun x => inferInstanceAs (Decidable (x.1 ∈ rotations ∧ x.2 ∈ rotations))
instance : DecidablePred (· ∈ A) := fun x => inferInstanceAs (Decidable (x.1 ∈ rotations ∧ x.2 = 1))
instance : DecidablePred (· ∈ B) := fun x => inferInstanceAs (Decidable (x.1 = 1 ∧ x.2 ∈ rotations))
instance : DecidablePred (· ∈ four) := fun x => inferInstanceAs (Decidable (x.1 ∈ reflections ∧ x.2 ∈ reflections))

theorem card_rotations : Nat.card rotations = 5 := by rw [Nat.card_eq_fintype_card]; decide +kernel
theorem card_plane : Nat.card plane = 25 := by rw [Nat.card_eq_fintype_card]; decide +kernel
theorem card_A : Nat.card A = 5 := by rw [Nat.card_eq_fintype_card]; decide +kernel
theorem card_B : Nat.card B = 5 := by rw [Nat.card_eq_fintype_card]; decide +kernel
theorem card_four : Nat.card four = 4 := by rw [Nat.card_eq_fintype_card]; decide +kernel

instance elementary_four : IsElementaryAbelian 2 four where
  is_comm.comm := by
    intro x y
    apply Subtype.ext
    exact (show ∀ x ∈ four, ∀ y ∈ four, x * y = y * x by decide +kernel) x x.property y y.property
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
    intro x
    apply Subtype.ext
    exact (show ∀ x ∈ four, x ^ 2 = 1 by decide +kernel) x x.property)

theorem normalizes_plane : four ≤ normalizer (plane : Set M) := by
  intro v hv
  exact (show ∀ v ∈ four, ∀ x : M, x ∈ plane ↔ v * x * v⁻¹ ∈ plane by decide +kernel) v hv

theorem normalizes_A : four ≤ normalizer (A : Set M) := by
  intro v hv
  exact (show ∀ v ∈ four, ∀ x : M, x ∈ A ↔ v * x * v⁻¹ ∈ A by decide +kernel) v hv

theorem normalizes_B : four ≤ normalizer (B : Set M) := by
  intro v hv
  exact (show ∀ v ∈ four, ∀ x : M, x ∈ B ↔ v * x * v⁻¹ ∈ B by decide +kernel) v hv

theorem A_le_plane : A ≤ plane := fun _ h => ⟨h.1, mem_bot.mp h.2 ▸ rotations.one_mem⟩
theorem B_le_plane : B ≤ plane := fun _ h => ⟨mem_bot.mp h.1 ▸ rotations.one_mem, h.2⟩

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private theorem eq_of_common_nonidentity {H : Type*} [Group H] [Finite H]
    (L K : Subgroup H) (hL : Nat.card L = 5) (hK : Nat.card K = 5)
    (x : H) (hxL : x ∈ L) (hxK : x ∈ K) (hx : x ≠ 1) : L = K := by
  apply eq_of_le_of_card_ge _ (hK.trans hL.symm).le
  intro y hy
  have hyz := mem_zpowers_of_prime_card hL
    (show (⟨x, hxL⟩ : L) ≠ 1 from fun h => hx (congrArg Subtype.val h)) (g' := ⟨y, hy⟩)
  obtain ⟨n, hn⟩ := hyz
  have he : x ^ n = y := congrArg Subtype.val hn
  exact he ▸ K.zpow_mem hxK n

/-- A coordinate reflection has exactly the two coordinate lines as invariant five-subgroups. -/
theorem fixed_lines (L : Subgroup M) (hL : Nat.card L = 5) (hLP : L ≤ plane) :
    (∀ v ∈ four, v ∈ normalizer (L : Set M)) ↔ L = A ∨ L = B := by
  constructor
  · intro hn
    by_cases hLA : ∃ x ∈ L, x.1 ≠ 1
    · obtain ⟨x, hx, hx1⟩ := hLA
      let v : M := (.sr 0, 1)
      have hv : v ∈ four := by decide +kernel
      have hc : v * x * v⁻¹ ∈ L := (hn v hv x).mp hx
      let y := x * (v * x * v⁻¹)⁻¹
      have hy : y ∈ L := L.mul_mem hx (L.inv_mem hc)
      have hyA : y ∈ A ∧ y ≠ 1 :=
        (show ∀ x ∈ plane, x.1 ≠ 1 →
          x * (((DihedralGroup.sr 0, 1) : M) * x * (DihedralGroup.sr 0, 1)⁻¹)⁻¹ ∈ A ∧
          x * (((DihedralGroup.sr 0, 1) : M) * x * (DihedralGroup.sr 0, 1)⁻¹)⁻¹ ≠ 1
          by decide +kernel) x (hLP hx) hx1
      exact Or.inl (eq_of_common_nonidentity L A hL card_A y hy hyA.1 hyA.2)
    · right
      apply eq_of_le_of_card_ge _ (card_B.trans hL.symm).le
      intro x hx
      exact ⟨mem_bot.mpr (by by_contra h; exact hLA ⟨x, hx, h⟩), (hLP hx).2⟩
  · rintro (rfl | rfl)
    · exact fun _ h => normalizes_A h
    · exact fun _ h => normalizes_B h

theorem four_inf_plane : ∀ x ∈ four, x ∈ plane → x = 1 := by decide +kernel

theorem rotations_of_fifth_power : ∀ x : D10, x ^ 5 = 1 → x ∈ rotations := by decide +kernel

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.SylowAction.SourceFourGroup.Model
