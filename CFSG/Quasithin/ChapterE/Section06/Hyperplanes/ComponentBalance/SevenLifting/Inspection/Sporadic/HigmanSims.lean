module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.Sporadic.Reduction
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSOuter
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.StructureTransport
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Basic
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex

/-!
# The HS seven-component inspection from its involution table

The two inner rows have orders 7680 and 2880, so neither can contain A₇ or
its perfect central triple cover. Consequently a two-subgroup P fixing a
seven subgroup has trivial intersection with Inn(HS). The actual map from
the permutation normalizer quotient onto Out(HS), together with the checked
normalizer index, then gives |P| dividing two.

For nontrivial P, its common fixed subgroup is therefore exactly the fixed
subgroup of its unique involution. The outer E₁₆-by-S₅ row has order 1920.
In the S₈ row, the intrinsic component is A₈, of order 20160, whereas both
seven models have order at most 7560. The proof retains the embedded subgroup
and its component membership throughout this identification.

The precise involution table is the sole explicit input. This conditional
helper does not assert that the remaining outer-table calculations are proved.
No simplicity, perfectness, action or component-exclusion premise is added.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the inspection
in E.6.18, printed p.252; Theorem C, printed p.33; 16.1.5(10), printed p.1172.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SporadicInspection
open Chapter16.OtherPreliminaries.JankoTwoHigmanSims
open Sporadic.LeechRelated.HS

private theorem outer_card_dvd_two : Nat.card (MulAut.Outer Carrier) ∣ 2 := by
  have hd := Subgroup.card_dvd_of_surjective (generated.normalizerOuterHom)
    (generated.normalizerOuterHom_surjective
      (normalizer_surjective_of_pointStabilizer_map pointStabilizer_map))
  rw [← index_eq_card] at hd
  exact hd.trans normalizer_relIndex_dvd_two

private theorem inner_fixed_card
    (rows : ∀ r : MulAut Carrier, orderOf r = 2 → HSInvolutionAlternative r)
    (r : MulAut Carrier) (hr : orderOf r = 2) (hi : ∃ g, r = MulAut.conj g) :
    ¬ 2520 ∣ Nat.card r.fixedSubgroup := by
  rcases rows r hr with ⟨_, h⟩ | ⟨hn, _⟩
  · rcases h with h | he
    · rw [HSInner.coreExtension_card h]
      decide
    · obtain ⟨e⟩ := he
      rw [Nat.card_congr e.toEquiv, Nat.card_prod, AlternatingSix.ShadowLocal.card_aut]
      norm_num [C2]
  · exact (hn hi).elim

private theorem inner_intersection_eq_bot
    (rows : ∀ r : MulAut Carrier, orderOf r = 2 → HSInvolutionAlternative r)
    (P : Subgroup (MulAut Carrier)) (hp : IsPGroup 2 P)
    (L : Subgroup Carrier) (hLF : L ≤ FixedPoints.subgroup P Carrier) (hs : IsSeven L) :
    P ⊓ MulAut.innerSubgroup Carrier = ⊥ := by
  let K := P ⊓ MulAut.innerSubgroup Carrier
  have hk : IsPGroup 2 K := hp.of_injective (inclusion inf_le_left)
    (inclusion_injective inf_le_left)
  by_contra hn
  obtain ⟨a, ha, hane⟩ := K.bot_or_exists_ne_one.resolve_left hn
  have hne : (⟨a, ha⟩ : K) ≠ 1 := fun h => hane (congrArg Subtype.val h)
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := K) 2
    ((hk.dvd_orderOf hne).trans (orderOf_dvd_natCard (x := (⟨a, ha⟩ : K))))
  have ht' : orderOf (t : MulAut Carrier) = 2 := (Subgroup.orderOf_coe t).trans ht
  have hi : ∃ g, (t : MulAut Carrier) = MulAut.conj g := by
    obtain ⟨g, hg⟩ := t.property.2
    exact ⟨g, hg.symm⟩
  have hLt : L ≤ (t : MulAut Carrier).fixedSubgroup := by
    intro x hx
    exact (MulAut.mem_fixedSubgroup _ _).mpr (hLF hx ⟨t, t.property.1⟩)
  exact inner_fixed_card rows t ht' hi ((seven_card_dvd hs).trans (card_dvd_of_le hLt))

private theorem actor_card_dvd_two (P : Subgroup (MulAut Carrier))
    (hd : P ⊓ MulAut.innerSubgroup Carrier = ⊥) : Nat.card P ∣ 2 := by
  have hi := (MulAut.innerSubgroup Carrier).relIndex_dvd_index_of_normal (K := P)
  rw [← inf_relIndex_right, inf_comm _ P, hd, relIndex_bot_left] at hi
  exact hi.trans outer_card_dvd_two

private theorem fixed_eq_of_card_two (P : Subgroup (MulAut Carrier))
    (hc : Nat.card P = 2) (t : P) (ht : orderOf t = 2) :
    FixedPoints.subgroup P Carrier = (t : MulAut Carrier).fixedSubgroup := by
  obtain ⟨u, hu, huniq⟩ := (Nat.card_eq_two_iff' (1 : P)).mp hc
  have htne : t ≠ 1 := by
    intro h
    simp [h] at ht
  have htu := huniq t htne
  ext x
  constructor
  · intro hx
    exact (MulAut.mem_fixedSubgroup _ _).mpr (hx t)
  · intro hx a
    by_cases ha : a = 1
    · subst a
      rfl
    · have hat : a = t := (huniq a ha).trans htu.symm
      subst a
      exact (MulAut.mem_fixedSubgroup _ _).mp hx

private theorem elementary_extension_card {C : Type*} [Group C]
    (h : IsHSElementaryExtension C) : Nat.card C = 1920 := by
  obtain ⟨Q, hn, ⟨eQ⟩, ⟨eR⟩⟩ := h
  let := hn
  rw [card_eq_card_quotient_mul_card_subgroup Q, Nat.card_congr eQ.toEquiv,
    Nat.card_congr eR.toEquiv]
  norm_num [E16, C2, S5, Nat.card_perm, Fintype.card_perm, Nat.factorial]

private theorem seven_card_le {L : Subgroup Carrier} (hs : IsSeven L) :
    Nat.card L ≤ 7560 := by
  have hA : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [nat_card_alternatingGroup]
    norm_num
  rcases hs with ha | hc
  · obtain ⟨e⟩ := ha
    rw [Nat.card_congr e.toEquiv, hA]
    decide
  · obtain ⟨_, ⟨ez⟩, ⟨eq⟩⟩ := hc
    rw [card_eq_card_quotient_mul_card_subgroup (center L),
      Nat.card_congr ez.toEquiv, Nat.card_congr eq.toEquiv, hA]
    norm_num

/-- The exact HS involution table excludes seven components in the common
fixed subgroup of every nontrivial two-subgroup of the full automorphism group. -/
theorem higman_sims
    (rows : ∀ r : MulAut Carrier, orderOf r = 2 → HSInvolutionAlternative r) :
    SevenActionInspection Carrier := by
  intro P hp L hLF hcomp hs
  by_contra hn
  have hd := inner_intersection_eq_bot rows P hp L hLF hs
  obtain ⟨a, ha, hane⟩ := P.bot_or_exists_ne_one.resolve_left hn
  have hne : (⟨a, ha⟩ : P) ≠ 1 := fun h => hane (congrArg Subtype.val h)
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := P) 2
    ((hp.dvd_orderOf hne).trans (orderOf_dvd_natCard (x := (⟨a, ha⟩ : P))))
  have ht' : orderOf (t : MulAut Carrier) = 2 := (Subgroup.orderOf_coe t).trans ht
  have hcard : Nat.card P = 2 := Nat.dvd_antisymm (actor_card_dvd_two P hd)
    (ht ▸ orderOf_dvd_natCard (x := t))
  have hfixed := fixed_eq_of_card_two P hcard t ht
  have hLt : L ≤ (t : MulAut Carrier).fixedSubgroup := hfixed ▸ hLF
  have hcomponent : IsComponent (t : MulAut Carrier).fixedSubgroup
      (L.subgroupOf (t : MulAut Carrier).fixedSubgroup) := hfixed ▸ hcomp
  have hdiv := (seven_card_dvd hs).trans (card_dvd_of_le hLt)
  rcases rows t ht' with ⟨hi, _⟩ | ⟨_, h⟩
  · exact inner_fixed_card rows t ht' hi hdiv
  · rcases h with he | he
    · obtain ⟨e⟩ := he
      obtain ⟨f⟩ := HSOuter.component_equiv_alternating e _ hcomponent
      have hLcard : Nat.card L = 20160 := by
        rw [← Nat.card_congr (subgroupOfEquivOfLe hLt).toEquiv,
          Nat.card_congr f.toEquiv, nat_card_alternatingGroup]
        norm_num
      have hbound := seven_card_le hs
      omega
    · rw [elementary_extension_card he] at hdiv
      norm_num at hdiv

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SporadicInspection
