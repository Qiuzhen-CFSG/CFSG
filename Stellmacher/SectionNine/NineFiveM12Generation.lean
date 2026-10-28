module

public import Stellmacher.SectionNine.NineFiveM12Data
public import Theory.Mathieu.M12.Properties.Simplicity
public import Mathlib.GroupTheory.IndexNormal

@[expose] public section

open scoped Pointwise

noncomputable section

namespace Stellmacher.SectionNine.M12Realization

open Sporadic.Mathieu

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def generationFirstPerm : Equiv.Perm (Fin 12) :=
  List.formPerm [1, 0, 3] * List.formPerm [2, 4, 5] *
    List.formPerm [6, 9, 10] * List.formPerm [7, 11, 8]

def generationSecondPerm : Equiv.Perm (Fin 12) :=
  List.formPerm [1, 6, 11] * List.formPerm [5, 8, 10] * List.formPerm [7, 0, 9]

theorem generationFirstPerm_mem : generationFirstPerm ∈ M12 := by
  apply (mem_M12_iff _).mpr
  have hblocks : generationFirstPerm • m12Blocks = m12Blocks := by decide +kernel
  exact_mod_cast hblocks

theorem generationSecondPerm_mem : generationSecondPerm ∈ M12 := by
  apply (mem_M12_iff _).mpr
  have hblocks : generationSecondPerm • m12Blocks = m12Blocks := by decide +kernel
  exact_mod_cast hblocks

def generationFirst : M12 := ⟨generationFirstPerm, generationFirstPerm_mem⟩

def generationSecond : M12 := ⟨generationSecondPerm, generationSecondPerm_mem⟩

theorem generation_centerPlane_mem_iff (element : M12) :
    element ∈ centerPlane ↔ element = 1 ∨ element = centerElement ∨
      element = planeElement ∨ element = centerElement * planeElement := by
  apply Subgroup.mem_closure_pair_iff
  · apply Subtype.ext
    decide +kernel
  · apply Subtype.ext
    decide +kernel
  · change centerElement * planeElement = planeElement * centerElement
    apply Subtype.ext
    decide +kernel

private theorem generationFirst_conj_mem (element : M12) (hmem : element ∈ centerPlane) :
    generationFirst * element * generationFirst⁻¹ ∈ centerPlane := by
  rw [generation_centerPlane_mem_iff] at hmem ⊢
  rcases hmem with rfl | rfl | rfl | rfl <;>
    simp only [← Subtype.coe_inj] <;> decide +kernel

private theorem generationFirst_inv_conj_mem (element : M12)
    (hmem : element ∈ centerPlane) :
    generationFirst⁻¹ * element * generationFirst ∈ centerPlane := by
  rw [generation_centerPlane_mem_iff] at hmem ⊢
  rcases hmem with rfl | rfl | rfl | rfl <;>
    simp only [← Subtype.coe_inj] <;> decide +kernel

theorem generationFirst_mem : generationFirst ∈ firstLocal := by
  rw [firstLocal, Subgroup.mem_set_normalizer_iff]
  intro element
  constructor
  · exact generationFirst_conj_mem element
  · intro hmem
    have heq : generationFirst⁻¹ * (generationFirst * element * generationFirst⁻¹) *
        generationFirst = element := by group
    exact (congrArg (fun value : M12 => value ∈ centerPlane) heq).mp
      (generationFirst_inv_conj_mem _ hmem)

theorem generationSecond_mem : generationSecond ∈ secondLocal := by
  rw [secondLocal, Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  decide +kernel

theorem generation_order_five :
    orderOf (generationFirst * generationSecond * generationFirst * generationSecond) = 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  rw [← Subgroup.orderOf_coe]
  apply orderOf_eq_prime <;> decide +kernel

theorem generation_order_eleven :
    orderOf (generationFirst * generationSecond * generationFirst ^ 2 * generationSecond) = 11 := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  rw [← Subgroup.orderOf_coe]
  apply orderOf_eq_prime <;> decide +kernel

theorem generation_eq_top_of_card_dvd (subgroup : Subgroup M12)
    (h192 : 192 ∣ Nat.card subgroup) (h5 : 5 ∣ Nat.card subgroup)
    (h11 : 11 ∣ Nat.card subgroup) : subgroup = ⊤ := by
  let : IsSimpleGroup M12 := m12_isSimpleGroup
  have h10560 : 10560 ∣ Nat.card subgroup := by
    have hfirst := Nat.lcm_dvd h192 h5
    have hsecond := Nat.lcm_dvd hfirst h11
    norm_num at hsecond
    exact hsecond
  have hmul := subgroup.card_mul_index
  rw [m12_order] at hmul
  have hbound : subgroup.index ≤ 9 := by
    obtain ⟨multiple, hmultiple⟩ := h10560
    rw [hmultiple] at hmul
    have hpositive : 0 < multiple := by nlinarith
    nlinarith
  rcases subgroup.normalCore_normal.eq_bot_or_eq_top with hbot | htop
  · have hfactorial : subgroup.normalCore.index ∣ (subgroup.index).factorial := by
      rw [Subgroup.normalCore_eq_ker, Subgroup.index_ker, Subgroup.index_eq_card,
        ← Nat.card_perm]
      exact Subgroup.card_subgroup_dvd_card (MulAction.toPermHom M12 (M12 ⧸ subgroup)).range
    rw [hbot, Subgroup.index_bot, m12_order] at hfactorial
    have h11factorial : 11 ∣ (subgroup.index).factorial :=
      dvd_trans (by norm_num : 11 ∣ 95040) hfactorial
    have hlarge := (Nat.Prime.dvd_factorial (by decide : Nat.Prime 11)).mp h11factorial
    omega
  · exact top_unique (htop ▸ subgroup.normalCore_le)

theorem generation_eq_top_of_first_card (hfirst : Nat.card firstLocal = 192) :
    firstLocal ⊔ secondLocal = ⊤ := by
  let joined := firstLocal ⊔ secondLocal
  have hleft : generationFirst ∈ joined :=
    (show firstLocal ≤ joined from le_sup_left) generationFirst_mem
  have hright : generationSecond ∈ joined :=
    (show secondLocal ≤ joined from le_sup_right) generationSecond_mem
  apply generation_eq_top_of_card_dvd joined
  · simpa only [hfirst] using
      (Subgroup.card_dvd_of_le (show firstLocal ≤ joined from le_sup_left))
  · have hmem : generationFirst * generationSecond * generationFirst * generationSecond ∈ joined :=
      joined.mul_mem (joined.mul_mem (joined.mul_mem hleft hright) hleft) hright
    simpa only [Subgroup.orderOf_mk, generation_order_five] using
      orderOf_dvd_natCard (⟨_, hmem⟩ : joined)
  · have hmem : generationFirst * generationSecond * generationFirst ^ 2 * generationSecond ∈ joined :=
      joined.mul_mem (joined.mul_mem (joined.mul_mem hleft hright) (joined.pow_mem hleft 2)) hright
    simpa only [Subgroup.orderOf_mk, generation_order_eleven] using
      orderOf_dvd_natCard (⟨_, hmem⟩ : joined)


end Stellmacher.SectionNine.M12Realization
