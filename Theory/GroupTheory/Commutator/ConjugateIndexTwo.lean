module
public import Theory.GroupTheory.MutualBinaryActions
public import Theory.GroupTheory.Commutator.IndexTwoSaturation
public import Theory.GroupTheory.InvolutionCentralizerControl

/-!
# The line shared by conjugate abelian modules

Suppose V is abelian and normal in R, and Q centralizes V with index two
in R. If g normalizes R and V does not commute with its inverse conjugate,
that conjugate crosses Q, so it has the same commutator with V as R does.
Both mutual conjugation images have order at most two. Their commutator
therefore has order two; saturation on both sides makes g normalize, and
hence centralize, this literal subgroup.

This is the group-theoretic part of Aschbacher--Smith 12.6.16(2), printed
pp.826--827, combined manuscript of 1 March 2004. No module identification
or ambient simplicity is used here.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The shared commutator is the full R-moved subgroup, has order two, and is fixed by g. -/
theorem conjugate_commutator_card_two_and_fixed
    (V Q R : Subgroup G) [IsMulCommutative V]
    (hVR : V ≤ R) (hRV : R ≤ normalizer (V : Set G))
    (hQR : Q ≤ R) (hQC : Q ≤ centralizer (V : Set G))
    (hi : Q.relIndex R = 2) (g : G)
    (hR : R.map (MulAut.conj g).toMonoidHom = R)
    (hne : ⁅V,V.map (MulAut.conj g⁻¹).toMonoidHom⁆ ≠ ⊥) :
    ⁅V,V.map (MulAut.conj g⁻¹).toMonoidHom⁆ = ⁅V,R⁆ ∧
      Nat.card (⁅V,R⁆ : Subgroup G) = 2 ∧
      g ∈ centralizer (↑(⁅V,R⁆ : Subgroup G) : Set G) := by
  let c := (MulAut.conj g).toMonoidHom
  let d := (MulAut.conj g⁻¹).toMonoidHom
  let A := V.map d
  have hcancel (B : Subgroup G) : (B.map d).map c = B := by
    rw [map_map]
    have hh : c.comp d = MonoidHom.id G := by
      ext x
      simp [c,d,MulAut.conj_apply,mul_assoc]
    rw [hh,map_id]
  have hRi : R.map d = R := by
    apply map_injective (f := c) (MulAut.conj g).injective
    rw [hcancel,hR]
  have hAR : A ≤ R := (map_mono hVR).trans_eq hRi
  have hRA : R ≤ normalizer (A : Set G) := by
    rw [←hRi]
    exact (map_mono hRV).trans (V.le_normalizer_map d)
  have hVA : V ≤ normalizer (A : Set G) := hVR.trans hRA
  have hAV : A ≤ normalizer (V : Set G) := hAR.trans hRV
  have hAQ : ¬ A ≤ Q := by
    intro h
    exact hne (by rw [commutator_comm]; exact commutator_eq_bot_iff_le_centralizer.mpr (h.trans hQC))
  have hsat : ⁅V,A⁆ = ⁅V,R⁆ := by
    rw [commutator_comm V A,commutator_comm V R]
    exact (commutator_eq_of_centralizing_index_two V Q R A hRV hQR hQC hi hAR hAQ).symm
  have hf : (centralizer (V : Set G)).relIndex A ≤ 2 := by
    apply (relIndex_le_of_le_right hAR index_ne_zero_of_finite).trans
    exact (relIndex_le_of_le_left hQC index_ne_zero_of_finite).trans_eq hi
  have hh : (centralizer (A : Set G)).relIndex V ≤ 2 := by
    have hcent : (centralizer (A : Set G)).map c = centralizer (V : Set G) := by
      rw [←hcancel V]
      apply le_antisymm
      · exact map_centralizer_le_centralizer_image _ _
      · intro x hx
        refine ⟨MulAut.conj g⁻¹ x, ?_, ?_⟩
        · intro y hy
          apply (MulAut.conj g).injective
          simpa [c, MulAut.conj_apply, mul_assoc] using hx (c y) (mem_map_of_mem c hy)
        · simp [c,MulAut.conj_apply,mul_assoc]
    rw [←relIndex_map_map_of_injective (f := c) _ _ (MulAut.conj g).injective,hcent]
    apply (relIndex_le_of_le_right ((map_mono hVR).trans_eq hR) index_ne_zero_of_finite).trans
    exact (relIndex_le_of_le_left hQC index_ne_zero_of_finite).trans_eq hi
  have hc : Nat.card (⁅V,R⁆ : Subgroup G) = 2 := by
    have hu := commutator_card_le_two_of_mutual_centralizer_indices V A hAV hVA hf hh
    have hl := (one_lt_card_iff_ne_bot ⁅V,A⁆).mpr hne
    rw [hsat] at hu hl
    omega
  have hVgR : V.map c ≤ R := (map_mono hVR).trans_eq hR
  have hVgQ : ¬ V.map c ≤ Q := by
    intro h
    have hbot : ⁅V.map c,V⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr (h.trans hQC)
    have hm : (⁅V,A⁆).map c = ⊥ := by rw [map_commutator,hcancel]; exact hbot
    exact hne (map_injective (MulAut.conj g).injective (hm.trans (Subgroup.map_bot c).symm))
  have hsatg : ⁅V.map c,V⁆ = ⁅V,R⁆ := by
    rw [commutator_comm V R]
    exact (commutator_eq_of_centralizing_index_two V Q R (V.map c)
      hRV hQR hQC hi hVgR hVgQ).symm
  have hfix : (⁅V,R⁆).map c = ⁅V,R⁆ := by
    rw [←hsat,map_commutator,hcancel]
    exact hsatg.trans hsat.symm
  exact ⟨hsat,hc,normalizer_le_centralizer_of_card_two _ hc
    (mem_normalizer_iff_map_conj_eq.mpr hfix)⟩
end Subgroup
