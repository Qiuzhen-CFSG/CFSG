module
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.ElementaryRank
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.HolomorphGeometry
/-!
# Noncyclic normal elementary subgroups in the marked Aut(A6) Sylow model

An elementary subgroup normalized by an overgroup of the inner D8 lies
in the marked central four as soon as that overgroup escapes the natural
D8×C2. A small two-element coordinate test proves the placement; subgroup
orders then force equality with the four and the full Sylow overgroup.
This is the binary step in E.2.7, printed p.219, with all markings retained.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace AlternatingSix.ShadowLocal.Holomorph

private theorem invariant_involution_test : ∀ x v : Model,
    (¬ ∃ i, naturalEmbedding i = x) ∧ v ^ 2 = 1 ∧
    v * ((rotation^2)*v*(rotation^2)⁻¹) = ((rotation^2)*v*(rotation^2)⁻¹)*v ∧
    v * (reflection*v*reflection⁻¹) = (reflection*v*reflection⁻¹)*v ∧
    v * (x*v*x⁻¹) = (x*v*x⁻¹)*v →
    ∃ i, centralTranspositionEmbedding i = v := by
  decide +kernel

/-- An elementary subgroup normalized by an escaping Sylow overgroup
is contained in the actual central four of the natural intersection. -/
theorem normal_elementary_le_central_four
    (S E : Subgroup Model) (hDS : innerD ≤ S) (hout : ¬ S ≤ natural)
    [IsElementaryAbelian 2 E] (hn : S ≤ normalizer (E : Set Model)) :
    E ≤ centralTwo ⊔ transpositionSubgroup := by
  obtain ⟨x,hx,hxn⟩ := SetLike.not_le_iff_exists.mp hout
  intro v hv
  apply (mem_centralTwo_sup_transposition v).mpr
  apply invariant_involution_test x v
  refine ⟨(fun hi => hxn ((mem_natural x).mpr hi)),
    elemPow_eq_one_of_isElementaryAbelian v hv, ?_, ?_, ?_⟩
  · exact setLike_mul_comm hv ((mem_normalizer_iff.mp
      (hn (hDS (subset_closure (by simp)))) v).mp hv)
  · exact setLike_mul_comm hv ((mem_normalizer_iff.mp
      (hn (hDS (subset_closure (by simp)))) v).mp hv)
  · exact setLike_mul_comm hv ((mem_normalizer_iff.mp (hn hx) v).mp hv)

/-- Noncyclicity forces equality with that four-group. -/
theorem normal_elementary_eq_central_four
    (S E : Subgroup Model) (hDS : innerD ≤ S) (hout : ¬ S ≤ natural)
    [IsElementaryAbelian 2 E] (hn : S ≤ normalizer (E : Set Model))
    (hE : 2 < Nat.card E) : E = centralTwo ⊔ transpositionSubgroup := by
  have hle := normal_elementary_le_central_four S E hDS hout hn
  have hc : Nat.card (centralTwo ⊔ transpositionSubgroup : Subgroup Model) = 4 := by
    rw [←centralTranspositionEmbedding_range,
      ←Nat.card_congr (MonoidHom.ofInjective centralTranspositionEmbedding_injective).toEquiv]
    simp [E4,C2]
  have hd : Nat.card E ∣ 4 := hc ▸ card_dvd_of_le hle
  have hd' := Nat.mem_divisors.mpr ⟨hd,(by decide : 4 ≠ 0)⟩
  rw [show Nat.divisors 4 = ({1,2,4}:Finset ℕ) by decide] at hd'
  simp only [Finset.mem_insert,Finset.mem_singleton] at hd'
  exact eq_of_le_of_card_ge hle (by omega)
end AlternatingSix.ShadowLocal.Holomorph
namespace AlternatingSix.ShadowLocal.Holomorph
open Subgroup

theorem natural_eq_inner_sup_central_four :
    natural = innerD ⊔ (centralTwo ⊔ transpositionSubgroup) := by
  apply le_antisymm
  · apply (closure_le _).mpr
    intro x hx
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact (show innerD ≤ innerD ⊔ (centralTwo ⊔ transpositionSubgroup) from le_sup_left) (subset_closure (by simp))
    · exact (show centralTwo ⊔ transpositionSubgroup ≤ innerD ⊔ (centralTwo ⊔ transpositionSubgroup) from le_sup_right) ((show transpositionSubgroup ≤ centralTwo ⊔ transpositionSubgroup from le_sup_right) (mem_zpowers _))
    · exact (show innerD ≤ innerD ⊔ (centralTwo ⊔ transpositionSubgroup) from le_sup_left) (subset_closure (by simp))
  · refine sup_le ?_ (sup_le ?_ ?_)
    · exact closure_mono (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx ⊢; tauto)
    · apply zpowers_le.mpr
      have hr : rotation^2 ∈ natural := subset_closure (by simp)
      simpa [←pow_mul] using natural.pow_mem hr 2
    · exact zpowers_le.mpr (subset_closure (by simp))

theorem normal_elementary_forces_full_sylow
    (S E : Subgroup Model) (hDS : innerD ≤ S) (hout : ¬ S ≤ natural)
    [IsElementaryAbelian 2 E] (hn : S ≤ normalizer (E : Set Model))
    (hES : E ≤ S) (hE : 2 < Nat.card E) : S = ⊤ := by
  have he := normal_elementary_eq_central_four S E hDS hout hn hE
  have hNS : natural ≤ S := by
    rw [natural_eq_inner_sup_central_four,←he]
    exact sup_le hDS hES
  have hncard : Nat.card natural = 16 := by
    rw [Nat.card_congr naturalEquiv.toEquiv,Nat.card_prod,DihedralGroup.nat_card]
    simp [C2]
  have hlarge : 16 < Nat.card S := by
    by_contra! hh
    have heq := eq_of_le_of_card_ge hNS (by omega)
    exact hout heq.symm.le
  have hc := S.card_mul_index
  rw [card_model] at hc
  have hpos : 0 < S.index := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hi : S.index = 1 := by nlinarith
  exact index_eq_one.mp hi
end AlternatingSix.ShadowLocal.Holomorph
