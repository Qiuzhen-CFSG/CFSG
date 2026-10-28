module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FixedSpaces
public import Theory.Representation.PSL3Two.FourGroupGeometry.Normalizers.FourGroupCoverage
public import Theory.Representation.BinaryOffender.RatioFromStrong

/-!
# Rank-two reduction for the binary four-space offenders

On a four-dimensional binary SL₃(2)-module where every involution has a
fixed plane, every elementary actor has codimension at least two and rank
at most two. Thus no strong offender exists, and best offenders are exactly
the elementary four-groups fixing a plane. If each involution's displacement
is its fixed plane, all best offenders are quadratic.

Source: Aschbacher–Smith, B.4.8(2)–(3), printed p.91, combined manuscript
of 1 March 2004. These numerical deductions are used on the original
central-quotient and natural-submodule actions in `FourSpaceOffenders`.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.FourSpaceOffenders
open BinaryLinearThree
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) BinaryLinearThree.Group V)

theorem elementary_rank_le_two (A : Subgroup BinaryLinearThree.Group)
    (hA : IsElementaryTwo A) : rank A ≤ 2 := by
  let _ : IsElementaryAbelian 2 A := hA.2
  let f := MulAut.conj (G := BinaryLinearThree.Group)
  have hi : Function.Injective f :=
    MulAut.conj_injective_of_center_eq_bot Matrix.PSL3Two.center_eq_bot
  have hc := FourGroupGeometry.elementary_card_le_four (A.map f)
    (IsElementaryAbelian.map f)
  rw [Subgroup.card_map_of_injective hi] at hc
  have h := Nat.log_monotone (b := 2) hc
  exact h

theorem fixedCodim_ge_two
    (hdim : Module.finrank (ZMod 2) V = 4)
    (hInv : ∀ a : BinaryLinearThree.Group, orderOf a = 2 →
      Module.finrank (ZMod 2) (fixedSpace ρ (zpowers a)) = 2)
    {A : Subgroup BinaryLinearThree.Group} (hA : IsElementaryTwo A) :
    2 ≤ fixedCodim ρ A := by
  let _ : IsElementaryAbelian 2 A := hA.2
  obtain ⟨a, ha, hne⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
  have ho : orderOf a = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian a ha) hne
  have hle := Submodule.finrank_mono
    (fixedSpace_antitone ρ (zpowers_le.mpr ha))
  have hd := fixedCodim_add_finrank ρ A
  rw [hInv a ho] at hle
  omega

theorem no_strong
    (hdim : Module.finrank (ZMod 2) V = 4)
    (hInv : ∀ a : BinaryLinearThree.Group, orderOf a = 2 →
      Module.finrank (ZMod 2) (fixedSpace ρ (zpowers a)) = 2)
    (A : Subgroup BinaryLinearThree.Group) : ¬ IsStrongOffender ρ A := by
  intro hA
  have hl := fixedCodim_ge_two ρ hdim hInv hA.1
  have hr := elementary_rank_le_two A hA.1
  have hs := hA.2
  omega

theorem best_iff
    (hdim : Module.finrank (ZMod 2) V = 4)
    (hInv : ∀ a : BinaryLinearThree.Group, orderOf a = 2 →
      Module.finrank (ZMod 2) (fixedSpace ρ (zpowers a)) = 2)
    (A : Subgroup BinaryLinearThree.Group) :
    IsBestOffender ρ A ↔ IsElementaryTwo A ∧ rank A = 2 ∧
      Module.finrank (ZMod 2) (fixedSpace ρ A) = 2 := by
  rw [isBestOffender_iff_of_not_strong ρ
    (fun ⟨B, hB⟩ => no_strong ρ hdim hInv B hB)]
  constructor
  · rintro ⟨hA, he⟩
    have hl := fixedCodim_ge_two ρ hdim hInv hA
    have hr := elementary_rank_le_two A hA
    have hd := fixedCodim_add_finrank ρ A
    exact ⟨hA, by omega, by omega⟩
  · rintro ⟨hA, hr, hf⟩
    have hd := fixedCodim_add_finrank ρ A
    exact ⟨hA, by omega⟩

theorem best_fixedSpace_eq_involution
    (hdim : Module.finrank (ZMod 2) V = 4)
    (hInv : ∀ a : BinaryLinearThree.Group, orderOf a = 2 →
      Module.finrank (ZMod 2) (fixedSpace ρ (zpowers a)) = 2)
    {A : Subgroup BinaryLinearThree.Group} (hA : IsBestOffender ρ A)
    {a : BinaryLinearThree.Group} (ha : a ∈ A) (hne : a ≠ 1) :
    fixedSpace ρ A = fixedSpace ρ (zpowers a) := by
  let _ : IsElementaryAbelian 2 A := hA.1.2
  have ho : orderOf a = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian a ha) hne
  exact Submodule.eq_of_le_of_finrank_eq (fixedSpace_antitone ρ (zpowers_le.mpr ha))
    (((best_iff ρ hdim hInv A).mp hA).2.2.trans (hInv a ho).symm)

theorem best_quadratic
    (hdim : Module.finrank (ZMod 2) V = 4)
    (hInv : ∀ a : BinaryLinearThree.Group, orderOf a = 2 →
      subspaceCommutator ρ ⊤ (zpowers a) = fixedSpace ρ (zpowers a) ∧
      Module.finrank (ZMod 2) (fixedSpace ρ (zpowers a)) = 2)
    {A : Subgroup BinaryLinearThree.Group} (hA : IsBestOffender ρ A) :
    IsQuadratic ρ A := by
  let _ : IsElementaryAbelian 2 A := hA.1.2
  intro a ha b hb v
  by_cases hne : b = 1
  · simp [hne]
  have ho : orderOf b = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian b hb) hne
  have hv : ρ b v - v ∈ subspaceCommutator ρ ⊤ (zpowers b) :=
    Submodule.subset_span ⟨b, mem_zpowers b, v, Submodule.mem_top, rfl⟩
  rw [(hInv b ho).1,
    ← best_fixedSpace_eq_involution ρ hdim (fun t ht => (hInv t ht).2) hA hb hne] at hv
  exact hv ⟨a, ha⟩
end CFSG.Quasithin.ChapterB.NaturalExtensions.FourSpaceOffenders
