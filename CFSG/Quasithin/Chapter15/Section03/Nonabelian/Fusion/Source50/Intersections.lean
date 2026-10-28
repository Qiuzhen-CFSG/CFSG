module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Action
public import Theory.ElementaryAbelian.EightQuotientRank

/-!
# The starred involution and the hyperplane in 15.3.53

The three-dimensional commutator space lies in both intersections. Since
V escapes O₂(H), that intersection is a proper subgroup of the group of
order sixteen. The kernel-image formula therefore gives an actor of order
two, on the actual map H → H/O₂(H).

Source: Aschbacher–Smith, Lemma 15.3.53(2), printed p.1146.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50
variable {G : Type*} [Group G] [Finite G]

theorem intersections_of_commutator_card (d : CharacteristicTwo.LocalData G)
    (H : Subgroup G) (hVH : d.V ≤ H)
    (hUQ : localSpan d.ZS H ≤ H.pCoreIn 2)
    (hVQ : ¬ d.V ≤ H.pCoreIn 2)
    (hc : ⁅localSpan d.ZS H,d.V⁆ ≤ d.V ⊓ localSpan d.ZS H)
    (hcard : Nat.card (⁅localSpan d.ZS H,d.V⁆ : Subgroup G) = 8) :
    d.V ⊓ H.pCoreIn 2 = ⁅localSpan d.ZS H,d.V⁆ ∧
      d.V ⊓ localSpan d.ZS H = ⁅localSpan d.ZS H,d.V⁆ ∧
      Nat.card ((d.V.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) = 2 := by
  let C := ⁅localSpan d.ZS H,d.V⁆
  let R := d.V ⊓ H.pCoreIn 2
  have hCR : C ≤ R := hc.trans (inf_le_inf_left _ hUQ)
  have hlow : 8 ≤ Nat.card R := hcard ▸ card_le_of_le hCR
  have hupp : Nat.card R ≤ 16 := d.action.card_vector ▸ card_le_of_le (show R ≤ d.V from inf_le_left)
  have hne : Nat.card R ≠ 16 := by
    intro he
    have hr : R = d.V := eq_of_le_of_card_ge inf_le_left (by rw [he,d.action.card_vector])
    exact hVQ (hr ▸ (show R ≤ H.pCoreIn 2 from inf_le_right))
  have hd : Nat.card R ∣ 16 := d.action.card_vector ▸ card_dvd_of_le (show R ≤ d.V from inf_le_left)
  obtain ⟨k,hk⟩ := hd
  have hk2 : 2 ≤ k := by
    by_contra hn
    have : k=0 ∨ k=1 := by omega
    rcases this with rfl | rfl
    · simp at hk
    · exact hne (by simpa using hk.symm)
  have hRcard : Nat.card R = 8 := by nlinarith
  have hRC : R = C := (eq_of_le_of_card_ge hCR (by rw [hRcard,hcard])).symm
  have hVC : d.V ⊓ localSpan d.ZS H = C :=
    le_antisymm ((inf_le_inf_left _ hUQ).trans_eq hRC) hc
  refine ⟨hRC,hVC,?_⟩
  let q := QuotientGroup.mk' (pCore 2 H)
  have hker : Nat.card ((d.V.subgroupOf H) ⊓ q.ker : Subgroup H) = 8 := by
    rw [← card_map_of_injective H.subtype_injective]
    rw [map_inf _ _ _ H.subtype_injective, map_subgroupOf_eq_of_le hVH]
    rw [QuotientGroup.ker_mk']
    exact hRcard
  have hvcard : Nat.card (d.V.subgroupOf H) = 16 :=
    (Nat.card_congr (subgroupOfEquivOfLe hVH).toEquiv).trans d.action.card_vector
  have hp := IsElementaryAbelian.card_inf_ker_mul_card_map (d.V.subgroupOf H) q
  rw [hker,hvcard] at hp
  dsimp only [q] at hp
  omega

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50
