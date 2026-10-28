module

public import CFSG.Quasithin.ChapterI.Section04To05.Residues.CoreOrders
public import CFSG.Quasithin.ChapterI.Section04To05.Residues.NeighborKernels
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The S₆ exception in the original pair-core join

If the point core vanishes modulo the line core, it fixes every neighboring
point and lies in the plane core. The literal pair quotients give
|Q₁|=4|Q₀|, |Q₂|=2|Q₀| and |Q₁∩Q₂|=|Q₀|. Thus Q₀=Q₁∩Q₂ is
normalized by both G₀ and G₁₂, which generate G. D4 makes it trivial,
contradicting D5 and the trivial center of S₆.

Source: I.5.7(1), printed p.420. Counting the pair cores directly avoids
introducing any ambient finiteness or additional Sylow-order premise.
-/

public noncomputable section
namespace Quasithin.I5.DSystem
open Subgroup
variable {G : Type*} [Group G] (S : DSystem .C3 G)

private theorem digon_core_card (U : Subgroup SymmetricThreeProduct.G)
    (h : U = SymmetricThreeProduct.leftParabolic ∨ U = SymmetricThreeProduct.rightParabolic) :
    Nat.card (pCore 2 U) = 2 := by
  rcases h with rfl | rfl
  · rw [SymmetricThreeProduct.left_twoCore]
    exact SymmetricThreeProduct.card_ker_leftQuotientMap
  · rw [SymmetricThreeProduct.right_twoCore]
    exact SymmetricThreeProduct.card_ker_rightQuotientMap

theorem line_pair_core_card (j : Fin 3) (hj : j = 0 ∨ j = 2) :
    Nat.card ((S.pair 1 j).pCoreIn 2) = Nat.card (S.Q 1) * 2 := by
  obtain ⟨e, he⟩ := S.line_standard_quotientMark
  rw [S.pair_core_card 1 j e]
  congr 1
  apply digon_core_card
  rcases hj with rfl | rfl
  · exact he.imp And.left And.left
  · exact he.symm.imp And.right And.right

theorem plane_line_core_card :
    Nat.card ((S.pair 1 2).pCoreIn 2) = Nat.card (S.Q 2) * 4 := by
  obtain ⟨e, he⟩ := S.plane_standard_quotientMark
  have hc : Nat.card (pCore 2
      ((localParabolic S.family 2 1).map (S.localQuotientMap 2 e))) = 4 := by
    rcases he with h | h
    · rw [h.2]; exact Matrix.PSL3Two.lineParabolic_core_data.2
    · rw [h.2]; exact Matrix.PSL3Two.pointParabolic_core_data.2
  have hh := S.pair_core_card 2 1 e
  rw [hc] at hh
  simpa only [pair, inf_comm] using hh

theorem point_line_core_card_of_symmetric
    (e₀ : (S.family 0 ⧸ pCore 2 (S.family 0)) ≃*
      Theory.SpecificGroups.SymmetricSix.S6) :
    Nat.card ((S.pair 0 1).pCoreIn 2) = Nat.card (S.Q 0) * 8 := by
  obtain ⟨e, he⟩ := S.exists_standard_quotientMark 0 1 2 S.point_parabolics e₀
    Theory.SpecificGroups.SymmetricSix.duadStabilizer
    Theory.SpecificGroups.SymmetricSix.synthemeStabilizer (fun T => by
      obtain ⟨g, _, h⟩ := Theory.SpecificGroups.SymmetricSix.coatoms_over_sylow T
      exact ⟨g, h⟩)
  rw [S.pair_core_card 0 1 e]
  congr 1
  rcases he with h | h
  · rw [h.1]; exact Theory.SpecificGroups.SymmetricSix.duadCore_card
  · rw [h.1]; exact Theory.SpecificGroups.SymmetricSix.synthemeCore_card

theorem point_join_line_plane_pair : S.family 0 ⊔ S.pair 1 2 = ⊤ := by
  apply top_unique
  rw [← S.generate]
  apply iSup_le
  intro i
  fin_cases i
  · exact le_sup_left
  · have h := congrArg (Subgroup.map (S.family 1).subtype) S.line_parabolics_generate
    simp only [localParabolic, Subgroup.map_sup, subgroupOf_map_subtype,
      ← MonoidHom.range_eq_map, range_subtype] at h
    change S.family 1 ≤ _
    rw [← h]
    exact sup_le (inf_le_left.trans le_sup_left) (by
      simpa only [pair, inf_comm] using
        (le_sup_right : S.pair 1 2 ≤ S.family 0 ⊔ S.pair 1 2))
  · have h := congrArg (Subgroup.map (S.family 2).subtype) S.plane_parabolics_generate
    simp only [localParabolic, Subgroup.map_sup, subgroupOf_map_subtype,
      ← MonoidHom.range_eq_map, range_subtype] at h
    change S.family 2 ≤ _
    rw [← h]
    exact sup_le (inf_le_left.trans le_sup_left) le_sup_right

theorem core_card_product (i j : Fin 3) :
    Nat.card (S.Q i) * Nat.card (S.Q j) =
      Nat.card (S.Q i ⊓ S.Q j : Subgroup G) * Nat.card (S.Q i ⊔ S.Q j : Subgroup G) := by
  let : Finite S.T := Finite.of_injective (inclusion (S.T_le 0)) (inclusion_injective _)
  have hn : (S.Q j).subgroupOf S.T ≤ normalizer ((S.Q i).subgroupOf S.T) := by
    intro a ha
    apply (S.Q i).le_normalizer_comap S.T.subtype
    exact S.family_le_normalizer_Q i (S.T_le i (S.Q_le_T j ha))
  have h := card_mul_eq_card_inf_mul_card_sup_of_normalizes
    ((S.Q i).subgroupOf S.T) ((S.Q j).subgroupOf S.T) hn
  rw [← subgroupOf_sup (S.Q_le_T i) (S.Q_le_T j)] at h
  change Nat.card ((S.Q i).subgroupOf S.T) * Nat.card ((S.Q j).subgroupOf S.T) =
    Nat.card ((S.Q i ⊓ S.Q j).subgroupOf S.T) *
      Nat.card ((S.Q i ⊔ S.Q j).subgroupOf S.T) at h
  simpa only [Nat.card_congr (subgroupOfEquivOfLe (S.Q_le_T i)).toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe (S.Q_le_T j)).toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe (inf_le_left.trans (S.Q_le_T i))).toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe (sup_le (S.Q_le_T i) (S.Q_le_T j))).toEquiv] using h

theorem point_core_ne_bot_of_symmetric
    (e : (S.family 0 ⧸ pCore 2 (S.family 0)) ≃*
      Theory.SpecificGroups.SymmetricSix.S6) : S.Q 0 ≠ ⊥ := by
  intro hb
  have hq : pCore 2 (S.family 0) = ⊥ :=
    (map_eq_bot_iff_of_injective _ (S.family 0).subtype_injective).mp hb
  have hi : Function.Injective (S.localQuotientMap 0 e) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [S.localQuotientMap_ker, hq]
  have hz : center (S.family 0) = ⊥ := by
    apply le_bot_iff.mp
    intro a ha
    have hfa : S.localQuotientMap 0 e a ∈ center Theory.SpecificGroups.SymmetricSix.S6 := by
      rw [mem_center_iff]
      intro b
      obtain ⟨c, rfl⟩ := S.localQuotientMap_surjective 0 e b
      simpa only [map_mul] using congrArg (S.localQuotientMap 0 e) (mem_center_iff.mp ha c)
    rw [Theory.SpecificGroups.SymmetricSix.s6_center_eq_bot, mem_bot] at hfa
    exact (mem_bot).mpr (hi (hfa.trans (map_one _).symm))
  rcases S.nondegenerate rfl with h | h
  · exact h hz
  · rw [hq, card_bot] at h
    omega

theorem point_core_not_le_lineCore_of_symmetric
    (e : (S.family 0 ⧸ pCore 2 (S.family 0)) ≃*
      Theory.SpecificGroups.SymmetricSix.S6) : ¬ S.Q 0 ≤ S.Q 1 := by
  intro h01
  have h02 := S.point_core_le_planeCore_of_le_lineCore h01
  have h01c := S.point_line_core_card_of_symmetric e
  have h10c := S.line_pair_core_card 0 (Or.inl rfl)
  have h12c := S.line_pair_core_card 2 (Or.inr rfl)
  have h21c := S.plane_line_core_card
  have h01c' : Nat.card ((S.pair 1 0).pCoreIn 2) = Nat.card (S.Q 0) * 8 := by
    simpa only [pair, inf_comm] using h01c
  have hprod := S.core_card_product 1 2
  rw [← S.line_plane_core_join, h12c] at hprod
  let : Finite (S.Q 1) := Finite.of_injective
    (inclusion ((S.family 1).pCoreIn_le 2)) (inclusion_injective _)
  have hcancel : Nat.card (S.Q 2) = Nat.card (S.Q 1 ⊓ S.Q 2 : Subgroup G) * 2 := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := S.Q 1))
    calc
      Nat.card (S.Q 1) * Nat.card (S.Q 2) = _ := hprod
      _ = Nat.card (S.Q 1) * (Nat.card (S.Q 1 ⊓ S.Q 2 : Subgroup G) * 2) := by ring
  have hc : Nat.card (S.Q 1 ⊓ S.Q 2 : Subgroup G) = Nat.card (S.Q 0) := by omega
  let : Finite (S.Q 1 ⊓ S.Q 2 : Subgroup G) := Finite.of_injective
    (inclusion inf_le_left) (inclusion_injective _)
  have heq : S.Q 0 = S.Q 1 ⊓ S.Q 2 := eq_of_le_of_card_ge (le_inf h01 h02) hc.le
  have hn12 : S.pair 1 2 ≤ normalizer (S.Q 0 : Set G) := by
    rw [heq]
    exact (le_inf (inf_le_left.trans (S.family_le_normalizer_Q 1))
      (inf_le_right.trans (S.family_le_normalizer_Q 2))).trans
        inf_normalizer_le_normalizer_inf
  let : (S.Q 0).Normal := normalizer_eq_top_iff.mp (top_unique (by
    rw [← S.point_join_line_plane_pair]
    exact sup_le (S.family_le_normalizer_Q 0) hn12))
  exact S.point_core_ne_bot_of_symmetric e (S.normal_eq_bot _ (S.Q_le_T 0))

/-- The complete original C₃ point-line core identity, including the S₆ branch. -/
theorem point_line_core_join : (S.pair 0 1).pCoreIn 2 = S.Q 0 ⊔ S.Q 1 := by
  rcases S.point_C3 rfl with he | he
  · obtain ⟨e⟩ := he
    exact S.point_line_core_join_of_alternating e
  · obtain ⟨e⟩ := he
    obtain ⟨d, hd⟩ := S.line_standard_quotientMark
    have hc := digon_core_card _ (hd.imp And.left And.left)
    have h := S.pair_core_join_or_le 1 0 d (by rw [hc]; exact Nat.prime_two)
    rcases h with hh | hh
    · simpa only [pair, inf_comm, sup_comm] using hh
    · exact (S.point_core_not_le_lineCore_of_symmetric e hh).elim

end Quasithin.I5.DSystem
