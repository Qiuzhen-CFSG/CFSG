module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.Reduction
public import Theory.GroupTheory.PrimeRankFixedJoin

/-!
# The rank obstruction for the faithful-three-action branch

A faithful subgroup of order three in N_G(W) supplies an element outside
C_G(W). If such an element centralizes an elementary nine inside C_G(W),
their product is an elementary group of order 27 inside N_G(W). This
contradicts quasithinness because W is a nonidentity two-subgroup.

This is the elementary rank step needed in the single-block reduction in
the proof of E.6.14, Aschbacher–Smith, combined manuscript (1 March 2004),
printed p.251. Constructing the fixed nine from two actual blocks remains
a separate model argument; no such construction is asserted here.
-/

public section

open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces
variable {G : Type*} [Group G] [Finite G]

/-- Faithfulness is an actual nontrivial conjugation action by an order-three element. -/
theorem HasFaithfulThreeAction.exists_element {W : Subgroup G}
    (h : HasFaithfulThreeAction W) :
    ∃ x ∈ normalizer (W : Set G), orderOf x = 3 ∧ x ∉ centralizer (W : Set G) := by
  obtain ⟨A, hAW, hcard, hinj⟩ := h
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 3 (show 3 ∣ Nat.card A by rw [hcard])
  refine ⟨a, hAW a.property,
    (orderOf_injective A.subtype A.subtype_injective a).trans ha, ?_⟩
  intro hc
  let f := W.normalizerMonoidHom.comp (inclusion hAW)
  have hk : f a = 1 := by
    change inclusion hAW a ∈ W.normalizerMonoidHom.ker
    rw [normalizerMonoidHom_ker]
    exact hc
  have he : a = 1 := hinj (hk.trans (map_one f).symm)
  simp only [he, orderOf_one] at ha
  omega

/-- The normalizer of a nonidentity subspace has three-rank at most two. -/
theorem normalizer_threeRank_le_two
    {K : GroupClass} {T : Sylow 2 G} {M V W : Subgroup G}
    (h : HypothesisE61 K T M V) (hne : W ≠ ⊥) (hWV : W ≤ V) :
    primeRank 3 (normalizer (W : Set G)) ≤ 2 := by
  have hp : IsPGroup 2 W := T.isPGroup'.to_le (hWV.trans h.le_sylow)
  exact (h.simpleQTKE.twoLocal_sqtk
    (show IsTwoLocal (normalizer (W : Set G)) from ⟨W, hne, hp, rfl⟩)).stronglyQuasithin
      3 (by decide) (by decide)

/-- A nine-group in C_G(W) cannot be centralized by a three-element acting
nontrivially on W: their join would be an elementary group of order 27. -/
theorem no_fixed_nine
    {K : GroupClass} {T : Sylow 2 G} {M V W E : Subgroup G}
    (h : HypothesisE61 K T M V) (hne : W ≠ ⊥) (hWV : W ≤ V)
    [IsElementaryAbelian 3 E] (hcard : Nat.card E = 9)
    (hEW : E ≤ centralizer (W : Set G))
    {x : G} (hxN : x ∈ normalizer (W : Set G)) (hxo : orderOf x = 3)
    (hxC : x ∉ centralizer (W : Set G)) :
    ¬ E ≤ centralizer ({x} : Set G) := by
  intro hfix
  let N := normalizer (W : Set G)
  let F := E.subgroupOf N
  let y : N := ⟨x, hxN⟩
  have hEN : E ≤ N := hEW.trans (centralizer_le_normalizer _)
  let _ : IsElementaryAbelian 3 F := IsElementaryAbelian.subgroupOf hEN
  have hFc : Nat.card F = 3 ^ 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hEN).toEquiv).trans hcard
  have hy : orderOf y = 3 :=
    (orderOf_injective N.subtype N.subtype_injective y).symm.trans hxo
  have hyF : y ∉ F := fun he => hxC (hEW he)
  have hFy : F ≤ centralizer ({y} : Set N) := by
    intro e he
    apply mem_centralizer_singleton_iff.mpr
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hfix he))
  have hr := IsElementaryAbelian.primeRank_ge_of_fixed_join F y hy hyF hFy hFc
  have hu := normalizer_threeRank_le_two h hne hWV
  change 3 ≤ primeRank 3 (normalizer (W : Set G)) at hr
  omega

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces
