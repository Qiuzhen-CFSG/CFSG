module

public import Theory.GroupTheory.TwoLocalUniquenessControl
public import Theory.GroupTheory.NormalFourCentralizerSeparation

/-!
# An index-two centralizer under two-local uniqueness

If the involution centralizer in a Sylow two-subgroup has index two and
coincides with its centralizer in the unique maximal two-local overgroup,
its normalizer remains in that overgroup. The normalizer index congruence
then makes it Sylow in the full involution centralizer. Comparing centralizer
orders separates this involution from every element centralized by the Sylow.

Source application: Aschbacher–Smith (2.4.29), printed p.545.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem secondary_centralizer_sylow_of_index_two
    (T : Sylow 2 G)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (u : G) (hu2 : orderOf u = 2) (huT : u ∈ (T : Subgroup G))
    (hMu : M ⊓ centralizer ({u} : Set G) = (T : Subgroup G) ⊓ centralizer ({u} : Set G))
    (hi : ((T : Subgroup G) ⊓ centralizer ({u} : Set G)).relIndex (T : Subgroup G) = 2) :
    let Tu := (T : Subgroup G) ⊓ centralizer ({u} : Set G)
    normalizer (Tu : Set G) ≤ M ∧
      (∃ S : Sylow 2 (centralizer ({u} : Set G)),
        (S : Subgroup (centralizer ({u} : Set G))).map (centralizer ({u} : Set G)).subtype = Tu) ∧
      ∀ z : G, (T : Subgroup G) ≤ centralizer ({z} : Set G) → ¬ IsConj u z := by
  let C := centralizer ({u} : Set G)
  let Tu := (T : Subgroup G) ⊓ C
  have hp : IsPGroup 2 Tu := T.isPGroup'.to_le inf_le_left
  have hnT : (T : Subgroup G) ≤ normalizer (Tu : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (show Tu ≤ (T : Subgroup G) from inf_le_left)).mp
      (normal_of_index_eq_two hi)
  have hne : Tu ≠ ⊥ := by
    intro hb
    have huTu : u ∈ Tu := ⟨huT, mem_centralizer_singleton_iff.mpr rfl⟩
    have hu1 : u=1 := mem_bot.mp (hb ▸ huTu)
    norm_num [hu1] at hu2
  have hN : normalizer (Tu : Set G) ≤ M :=
    normalizer_le_of_unique_maximalTwoLocal hu hp hne hnT
  have hmax : ¬ 2 ∣ Tu.relIndex C := by
    apply not_dvd_relIndex_of_normalizer_inf_le Tu Tu C hp inf_le_right
    · simp only [relIndex_self]; decide
    · change normalizer (Tu : Set G) ⊓ centralizer ({u} : Set G) ≤
        (T : Subgroup G) ⊓ centralizer ({u} : Set G)
      rw [←hMu]
      exact inf_le_inf_right _ hN
  refine ⟨hN,?_,?_⟩
  · let S : Sylow 2 C := (hp.comap_subtype : IsPGroup 2 (Tu.subgroupOf C)).toSylow hmax
    exact ⟨S,map_subgroupOf_eq_of_le inf_le_right⟩
  · intro z hz
    apply not_isConj_of_sylow_centralizer_card_lt u z Tu (T : Subgroup G)
      hp T.isPGroup' inf_le_right hz hmax
    have hproper : Tu ≠ (T : Subgroup G) := by
      intro heq
      have hii : Tu.relIndex (T : Subgroup G)=2 := hi
      rw [heq,relIndex_self] at hii
      omega
    exact lt_of_le_of_ne (card_le_of_le inf_le_left)
      (fun heq => hproper (eq_of_le_of_card_ge inf_le_left heq.ge))

end Subgroup
