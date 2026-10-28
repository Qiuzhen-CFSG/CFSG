module
public import Theory.SpecificGroups.SymplecticFour.Sylow.InvariantSubspaces
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.ParabolicCores
public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.Alignment
public import Theory.SpecificGroups.SymplecticFour.BorelActionGeometry.Normalizers

/-!
# Characteristic-two coverage of the symplectic Borel

The standard Borel has a self-centralizing two-core: its unipotent Sylow
contains the point radical, whose full ambient centralizer lies in that
radical. Every characteristic-two overgroup of this Borel stabilizes the
unique Sylow point or plane, so is contained in a standard parabolic.

Source: Aschbacher--Smith 2.5.2(2), printed p.551.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
private theorem point_radical_le_unipotent : pointRadicalAmbient (F := F) ≤ unipotent := by
  rintro _ ⟨q, hq, rfl⟩
  rw [pointRadical_eq_element q hq]
  simp [mem_unipotent_iff, mem_borel_iff, pointRadicalElement, pointRadicalMatrix]

theorem borel_selfCentralizing_core {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n) :
    centralizer (pCore 2 (borel (F := F)) : Set (borel (F := F))) ≤ pCore 2 borel := by
  apply (inf_centralizer_pCoreIn_le_iff 2 borel).mp
  rw [EvenBorelTorus.borel_twoCoreIn hF]
  exact inf_le_right.trans ((centralizer_le point_radical_le_unipotent).trans
    ((pointRadicalAmbient_selfCentralizing hF hn).trans point_radical_le_unipotent))

omit [CharP F 2] in
theorem unipotent_ne_bot : unipotent (F := F) ≠ ⊥ := by
  intro he
  have hh : Nat.card (unipotent (F := F)) = 1 := card_eq_one.mpr he
  rw [card_unipotent] at hh
  have hF : 1 < Nat.card F := Finite.one_lt_card
  have hpow : 1 < Nat.card F ^ 4 := one_lt_pow₀ hF (by decide)
  omega

theorem borel_overgroup_parabolic_of_characteristicTwo
    (J : Subgroup (Sp F)) (hBJ : borel ≤ J)
    (hc : centralizer (pCore 2 J : Set J) ≤ pCore 2 J) :
    J ≤ pointParabolic ∨ J ≤ planeParabolic := by
  have hUJ : unipotent ≤ J := unipotent_le_borel.trans hBJ
  exact unipotent_overgroup_parabolic_of_characteristicTwo J hUJ
    (fun he => unipotent_ne_bot (bot_unique (he ▸ hUJ))) hc
end Theory.SpecificGroups.SymplecticFour
