module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Enumeration.Setup

/-!
# Maximum-order counting for the commuting-transposition action

An elementary subgroup meets the kernel inside its fixed subgroup. Counting
its kernel and image, and comparing the image order with the actual module's
fixed-space index, bounds its order by the kernel's order. Equality excludes
the double-transposition line. The centralizer profile remains an explicit
input here, to be constructed from the source coordinates separately.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the offender
counting in B.2.4 and B.3.2, applied in C.5.6, printed pp.157–158.
-/

public section
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Enumeration
open Subgroup
variable {T : Type*} [Group T] [Finite T]

omit [Finite T] in
private theorem kernel_image_card (σ : T →* Perm) (V B : Subgroup T)
    (hk : σ.ker = V) : Nat.card (V ⊓ B : Subgroup T) * Nat.card (B.map σ) = Nat.card B := by
  have hc := relIndex_mul_relIndex (⊥ : Subgroup T) (σ.ker ⊓ B) B bot_le inf_le_right
  have hc' : Nat.card (σ.ker ⊓ B : Subgroup T) * σ.ker.relIndex B = Nat.card B := by
    simpa only [relIndex_bot_left, inf_relIndex_right] using hc
  rw [relIndex_ker, hk] at hc'
  exact hc'

omit [Finite T] in
private theorem elementary_inf_le_fixed (V B : Subgroup T) [IsElementaryAbelian 2 B] :
    V ⊓ B ≤ V ⊓ centralizer (B : Set T) :=
  inf_le_inf_left _ (le_centralizer_iff_isMulCommutative.mpr inferInstance)

/-- The complete upper order bound, for every elementary subgroup. -/
theorem elementary_card_le_core (σ : T →* Perm) (V : Subgroup T)
    (hk : σ.ker = V) (hr : σ.range = ChapterB.Offenders.D 5)
    (hp : FixedProfile σ V) (B : Subgroup T) (hBe : IsElementaryAbelian 2 B) :
    Nat.card B ≤ Nat.card V := by
  let : IsElementaryAbelian 2 B := hBe
  have hc : Nat.card (V ⊓ B : Subgroup T) ≤
      Nat.card (V ⊓ centralizer (B : Set T) : Subgroup T) :=
    card_le_of_le (elementary_inf_le_fixed V B)
  have hi := card_le_fixedIndex (B.map σ) ((B.map_le_range σ).trans hr.le)
  calc
    Nat.card B = Nat.card (V ⊓ B : Subgroup T) * Nat.card (B.map σ) :=
      (kernel_image_card σ V B hk).symm
    _ ≤ Nat.card (V ⊓ centralizer (B : Set T) : Subgroup T) * fixedIndex (B.map σ) :=
      Nat.mul_le_mul hc hi
    _ = Nat.card V := hp.card_fixed B

/-- In particular the elementary kernel belongs to the full maximum-order family. -/
theorem core_mem_maxFamily (σ : T →* Perm) (V : Subgroup T)
    (hVe : IsElementaryAbelian 2 V) (hk : σ.ker = V)
    (hr : σ.range = ChapterB.Offenders.D 5) (hp : FixedProfile σ V) :
    V ∈ Stellmacher.elementaryAbelianMaxSubgroups (⊤ : Subgroup T) :=
  ⟨le_top, hVe, fun B _ hBe => elementary_card_le_core σ V hk hr hp B hBe⟩

/-- Any elementary subgroup of the kernel's order is a maximum member. -/
theorem mem_maxFamily_of_card_eq (σ : T →* Perm) (V : Subgroup T)
    (hk : σ.ker = V) (hr : σ.range = ChapterB.Offenders.D 5)
    (hp : FixedProfile σ V) (B : Subgroup T) (hBe : IsElementaryAbelian 2 B)
    (hcard : Nat.card B = Nat.card V) :
    B ∈ Stellmacher.elementaryAbelianMaxSubgroups (⊤ : Subgroup T) := by
  refine ⟨le_top, hBe, fun E _ hEe => ?_⟩
  rw [hcard]
  exact elementary_card_le_core σ V hk hr hp E hEe

/-- A maximum elementary subgroup has no deficit between its image order and
fixed-space index. This is the equality case needed to exclude the fifth image. -/
theorem maxFamily_image_card_eq (σ : T →* Perm) (V : Subgroup T)
    (hVe : IsElementaryAbelian 2 V) (hk : σ.ker = V)
    (hr : σ.range = ChapterB.Offenders.D 5) (hp : FixedProfile σ V)
    (B : Subgroup T) (hB : B ∈ Stellmacher.elementaryAbelianMaxSubgroups (⊤ : Subgroup T)) :
    Nat.card (B.map σ) = fixedIndex (B.map σ) := by
  let : IsElementaryAbelian 2 B := hB.2.1
  have hc : Nat.card (V ⊓ B : Subgroup T) ≤
      Nat.card (V ⊓ centralizer (B : Set T) : Subgroup T) :=
    card_le_of_le (elementary_inf_le_fixed V B)
  have hi := card_le_fixedIndex (B.map σ) ((B.map_le_range σ).trans hr.le)
  have hmax : Nat.card V ≤ Nat.card B := hB.2.2 V le_top hVe
  have hprod := kernel_image_card σ V B hk
  have hfix := hp.card_fixed B
  have hpos : 0 < Nat.card (V ⊓ centralizer (B : Set T) : Subgroup T) := Nat.card_pos
  have hle : Nat.card (V ⊓ centralizer (B : Set T) : Subgroup T) * fixedIndex (B.map σ) ≤
      Nat.card (V ⊓ centralizer (B : Set T) : Subgroup T) * Nat.card (B.map σ) := by
    calc
      _ = Nat.card V := hfix
      _ ≤ Nat.card B := hmax
      _ = Nat.card (V ⊓ B : Subgroup T) * Nat.card (B.map σ) := hprod.symm
      _ ≤ _ := Nat.mul_le_mul_right _ hc
  exact le_antisymm hi (by nlinarith)

/-- Every maximum member has one of the four required action images. -/
theorem maxFamily_image_cases (σ : T →* Perm) (V : Subgroup T)
    (hVe : IsElementaryAbelian 2 V) (hk : σ.ker = V)
    (hr : σ.range = ChapterB.Offenders.D 5) (hp : FixedProfile σ V)
    (B : Subgroup T) (hB : B ∈ Stellmacher.elementaryAbelianMaxSubgroups (⊤ : Subgroup T)) :
    B.map σ = ⊥ ∨ B.map σ = line 0 ∨ B.map σ = line 1 ∨
      B.map σ = ChapterB.Offenders.D 5 := by
  have hle := (B.map_le_range σ).trans hr.le
  have hn := (card_eq_fixedIndex_iff _ hle).mp (maxFamily_image_card_eq σ V hVe hk hr hp B hB)
  rcases subgroup_cases (B.map σ) hle with h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact (hn h).elim
  · exact Or.inr (Or.inr (Or.inr h))

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Enumeration
end
