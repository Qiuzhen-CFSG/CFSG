module

public import CFSG.Quasithin.ChapterI.Section04To05.Residues.KernelSeparation
public import Theory.GroupAction.SubgroupConjugation
public import Theory.GroupAction.FiveActionFixedOrderBound

/-!
# A genuine five-element acts nontrivially on the original point core

The normalizer of the base-line point kernel inside G₀ is precisely G₀₁:
maximality and the proved nonnormality exclude any larger subgroup. Hence
an element centralizing Q₀ lies in G₀₁. But that parabolic has order prime
to five, from the actual A₆/S₆ parabolic quotient and its two-group kernel.
Cauchy's theorem supplies a five-element in the original point group, and
it therefore moves Q₀.

Source: the local-action input in the final paragraph of I.5.15, p.424.
-/

public noncomputable section
namespace Quasithin.I5.DSystem
open Subgroup
variable {G : Type*} [Group G] (S : DSystem .C3 G)

theorem point_line_kernel_normalizer :
    (normalizer (S.Q 0 ⊓ S.Q 1 : Subgroup G)).subgroupOf (S.family 0) =
      localParabolic S.family 0 1 := by
  have hle : localParabolic S.family 0 1 ≤
      (normalizer (S.Q 0 ⊓ S.Q 1 : Subgroup G)).subgroupOf (S.family 0) :=
    fun a ha => S.pair_normalizes_point_line_kernel ⟨a.property, ha⟩
  rcases S.point_parabolics.left_maximal.le_iff.mp hle with ht | he
  · apply (S.point_line_kernel_not_normalized ?_).elim
    intro g hg
    exact (show (⟨g, hg⟩ : S.family 0) ∈
      (normalizer (S.Q 0 ⊓ S.Q 1 : Subgroup G)).subgroupOf (S.family 0) from ht ▸ mem_top _)
  · exact he

theorem point_core_centralizer_le_line :
    (centralizer (S.Q 0 : Set G)).subgroupOf (S.family 0) ≤
      localParabolic S.family 0 1 := by
  rw [← S.point_line_kernel_normalizer]
  intro a ha
  change a.val ∈ normalizer (S.Q 0 ⊓ S.Q 1 : Subgroup G)
  apply centralizer_le_normalizer ((S.Q 0 ⊓ S.Q 1 : Subgroup G) : Set G)
  exact centralizer_le (show S.Q 0 ⊓ S.Q 1 ≤ S.Q 0 from inf_le_left) ha

private theorem pair_card_coprime_five_of_model {K : Type*} [Group K] [Finite K]
    (e : (S.family 0 ⧸ pCore 2 (S.family 0)) ≃* K)
    (hc : (Nat.card ((localParabolic S.family 0 1).map (S.localQuotientMap 0 e))).Coprime 5) :
    (Nat.card (S.pair 0 1)).Coprime 5 := by
  let : Finite (S.pair 0 1) := Finite.of_injective
    (inclusion (show S.pair 0 1 ≤ S.family 0 from inf_le_left)) (inclusion_injective _)
  let f := S.pairQuotientMap 0 1 e
  have hh := f.ker.card_mul_index
  rw [index_ker, f.range_eq_top_of_surjective (S.pairQuotientMap_surjective 0 1 e), card_top] at hh
  obtain ⟨n, hn⟩ := (S.pairQuotientMap_ker_isTwoGroup 0 1 e).exists_card_eq
  rw [← hh, hn]
  exact ((by decide : Nat.Coprime 2 5).pow_left n).mul_left hc

theorem point_line_pair_card_coprime_five : (Nat.card (S.pair 0 1)).Coprime 5 := by
  rcases S.point_standard_quotientMark with ⟨e, he⟩ | ⟨e, he⟩
  · apply S.pair_card_coprime_five_of_model e
    rcases he with h | h
    · rw [h.1, Theory.SpecificGroups.SymmetricSix.a6DuadStabilizer_order]; decide
    · rw [h.1, Theory.SpecificGroups.SymmetricSix.a6SynthemeStabilizer_order]; decide
  · apply S.pair_card_coprime_five_of_model e
    rcases he with h | h
    · rw [h.1, Theory.SpecificGroups.SymmetricSix.duadStabilizer_order]; decide
    · rw [h.1, Theory.SpecificGroups.SymmetricSix.synthemeStabilizer_order]; decide

theorem exists_point_five_element : ∃ a : S.family 0, orderOf a = 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  apply exists_prime_orderOf_dvd_card' 5
  apply dvd_trans _ (card_quotient_dvd_card (pCore 2 (S.family 0)))
  rcases S.point_C3 rfl with he | he
  · obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  · obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
    decide

theorem point_five_not_centralizes_core (a : S.family 0) (ha : orderOf a = 5) :
    a.val ∉ centralizer (S.Q 0 : Set G) := by
  intro hc
  have hl := S.point_core_centralizer_le_line hc
  let b : S.pair 0 1 := ⟨a.val, a.property, hl⟩
  have hb : orderOf b = 5 := by
    exact (Subgroup.orderOf_mk _ _).trans ((Subgroup.orderOf_mk _ a.property).symm.trans ha)
  have hd : 5 ∣ Nat.card (S.pair 0 1) := hb ▸ orderOf_dvd_natCard b
  have hh := S.point_line_pair_card_coprime_five
  exact (by decide : ¬ Nat.Coprime 5 5) (hh.coprime_dvd_left hd)

end Quasithin.I5.DSystem
