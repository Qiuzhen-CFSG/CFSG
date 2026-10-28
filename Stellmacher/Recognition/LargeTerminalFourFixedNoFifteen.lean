module

public import Stellmacher.Recognition.LargeTerminalFourFixedLocalData
public import Stellmacher.Recognition.LargeTerminalFourFixedThreeSubgroup
public import Theory.GroupTheory.SolvableFiveNormalizer

/-!
# The odd-order exclusion for a five-fixed involution

Normalizer confinement gives the actual order-five subgroup ambient Sylow
status and bounds its normalizer order by a divisor of 20480. In the solvable
centralizer of a five-fixed involution, a factor of three
produces a nontrivial three-subgroup centralized by the involution, normalized
by the actual five-subgroup, and with trivial five-centralizer. The terminal
four-fixed subgroup theorem excludes this configuration, proving that fifteen
cannot divide the involution centralizer order. This applies in particular to
the noncyclic four-fixed alternative; noncyclicity and the residual conditions
are not needed for this step.

The earlier reduction using an explicit bound on the three-part is retained
as a separate interface.

Source: Thompson VI, printed p.630, the final four-group contradiction.
-/

namespace Stellmacher.Recognition

open Later SectionsFiveToSeven Subgroup

universe u

/-- The Hall-theoretic reduction of the fixed-involution exclusion. The
three-part bound is explicit: solvability alone does not suffice. -/
public theorem LargeTerminalContext.not_three_dvd_fixed_involution_centralizer_of_not_eightyone_dvd
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5)
    (hN : normalizer (A : Set G) ≤ ctx.second)
    (y : G) (hy : y ∈ centralizer (A : Set G)) (hy2 : orderOf y = 2)
    (h81 : ¬ 81 ∣ Nat.card (centralizer ({y} : Set G))) :
    ¬ 3 ∣ Nat.card (centralizer ({y} : Set G)) := by
  let C := centralizer ({y} : Set G)
  obtain ⟨P, hP⟩ := ctx.exists_sylow_five_of_normalizer_le_second hS A hA hN
  have hPC : (P : Subgroup G) ≤ C := by
    rw [hP]
    intro a ha
    exact mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp hy a ha)
  let PC := P.subtype hPC
  intro h3
  have hsolv := (ctx.localStructure C
    (Theory.GroupTheory.isTwoLocal_involution_centralizer hy2)).1
  have hd := PC.three_dvd_card_normalizer_of_not_eightyone_dvd hsolv h81 h3
  have hmap : (normalizer (PC : Set C)).map C.subtype ≤ normalizer (A : Set G) := by
    change (normalizer (((P : Subgroup G).subgroupOf C) : Set C)).map C.subtype ≤ _
    have h := le_normalizer_map (H := (P : Subgroup G).subgroupOf C) C.subtype
    rw [map_subgroupOf_eq_of_le hPC] at h
    rwa [hP] at h ⊢
  have hdiv : Nat.card (normalizer (PC : Set C)) ∣ 20480 := by
    rw [← card_map_of_injective C.subtype_injective]
    exact ctx.second_card_of_large_card hS ▸ card_dvd_of_le (hmap.trans hN)
  have hbad := hd.trans hdiv
  norm_num at hbad

/-- Excluding 81 from the fixed involution centralizer is sufficient for
the final exclusion of 15. -/
public theorem LargeTerminalContext.not_fifteen_dvd_fixed_involution_centralizer_of_not_eightyone_dvd
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5)
    (hN : normalizer (A : Set G) ≤ ctx.second)
    (y : G) (hy : y ∈ centralizer (A : Set G)) (hy2 : orderOf y = 2)
    (h81 : ¬ 81 ∣ Nat.card (centralizer ({y} : Set G))) :
    ¬ 15 ∣ Nat.card (centralizer ({y} : Set G)) := by
  intro h15
  exact ctx.not_three_dvd_fixed_involution_centralizer_of_not_eightyone_dvd
    hS A hA hN y hy hy2 h81 ((by decide : 3 ∣ 15).trans h15)

/-- A factor of three yields a concrete subgroup obstruction, without a bound
on the three-part or on the full involution-centralizer core. The resulting
three-subgroup is normalized by the actual five-subgroup and has trivial
five-centralizer. -/
public theorem LargeTerminalContext.exists_three_subgroup_of_three_dvd_fixed_involution_centralizer
    {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5)
    (hN : normalizer (A : Set G) ≤ ctx.second)
    (y : G) (hy : y ∈ centralizer (A : Set G)) (hy2 : orderOf y = 2)
    (h3 : 3 ∣ Nat.card (centralizer ({y} : Set G))) :
    ∃ T : Subgroup G, IsPGroup 3 T ∧ T ≠ ⊥ ∧
      T ≤ centralizer ({y} : Set G) ∧ A ≤ normalizer (T : Set G) ∧
      T ⊓ centralizer (A : Set G) = ⊥ := by
  let C := centralizer ({y} : Set G)
  obtain ⟨P, hP⟩ := ctx.exists_sylow_five_of_normalizer_le_second hS A hA hN
  have hPC : (P : Subgroup G) ≤ C := by
    rw [hP]
    intro a ha
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hy a ha)
  let PC := P.subtype hPC
  have hPCcard : Nat.card PC = 5 := by
    change Nat.card ((P : Subgroup G).subgroupOf C) = 5
    rw [Nat.card_congr (subgroupOfEquivOfLe hPC).toEquiv, hP, hA]
  have hmapP : (PC : Subgroup C).map C.subtype = A := by
    change ((P : Subgroup G).subgroupOf C).map C.subtype = A
    rw [map_subgroupOf_eq_of_le hPC, hP]
  have hNC : (normalizer (PC : Set C)).map C.subtype ≤ normalizer (A : Set G) := by
    have hh := le_normalizer_map (H := (PC : Subgroup C)) C.subtype
    rwa [hmapP] at hh
  have hN3 : ¬ 3 ∣ Nat.card (normalizer (PC : Set C)) := by
    intro hh
    have hd : Nat.card (normalizer (PC : Set C)) ∣ 20480 := by
      rw [← card_map_of_injective C.subtype_injective]
      exact ctx.second_card_of_large_card hS ▸ card_dvd_of_le (hNC.trans hN)
    have hbad := hh.trans hd
    norm_num at hbad
  have hsolv := (ctx.localStructure C
    (Theory.GroupTheory.isTwoLocal_involution_centralizer hy2)).1
  obtain ⟨T, hT, hTne, hPT, hfixed⟩ :=
    PC.exists_normalized_three_subgroup_of_not_three_dvd_normalizer hsolv hPCcard hN3 h3
  refine ⟨T.map C.subtype, hT.map C.subtype, ?_, map_subtype_le _, ?_, ?_⟩
  · intro he
    apply hTne
    apply Subgroup.card_eq_one.mp
    have hh := Subgroup.card_eq_one.mpr he
    rwa [card_map_of_injective C.subtype_injective] at hh
  · rw [← hmapP]
    exact (map_mono hPT).trans (le_normalizer_map C.subtype)
  · apply eq_bot_iff.mpr
    rintro x ⟨⟨t, ht, rfl⟩, hx⟩
    have htC : t ∈ centralizer (PC : Set C) := by
      apply mem_centralizer_iff.mpr
      intro a ha
      apply Subtype.ext
      exact mem_centralizer_iff.mp hx a (hmapP ▸ mem_map_of_mem C.subtype ha)
    have ht1 : t = 1 := show t ∈ (⊥ : Subgroup C) from hfixed ▸ ⟨ht, htC⟩
    simpa using congrArg C.subtype ht1

/-- An alternative to the three-part bound: it suffices to exclude nontrivial
three-subgroups centralized by the involution and normalized fixed-point-freely
by the given five-subgroup. The structural exclusion remains an explicit input. -/
public theorem LargeTerminalContext.not_fifteen_dvd_fixed_involution_centralizer_of_three_subgroup_exclusion
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5)
    (hN : normalizer (A : Set G) ≤ ctx.second)
    (y : G) (hy : y ∈ centralizer (A : Set G)) (hy2 : orderOf y = 2)
    (hexclude : ∀ T : Subgroup G, IsPGroup 3 T →
      T ≤ centralizer ({y} : Set G) → A ≤ normalizer (T : Set G) →
      T ⊓ centralizer (A : Set G) = ⊥ → T = ⊥) :
    ¬ 15 ∣ Nat.card (centralizer ({y} : Set G)) := by
  intro h15
  obtain ⟨T, hT, hTne, hTC, hAT, hfixed⟩ :=
    ctx.exists_three_subgroup_of_three_dvd_fixed_involution_centralizer
      hS A hA hN y hy hy2 ((by decide : 3 ∣ 15).trans h15)
  exact hTne (hexclude T hT hTC hAT hfixed)

/-- Normalizer confinement and the actual four-element five-fixed subgroup
exclude a factor of three from every five-fixed involution centralizer. -/
public theorem LargeTerminalContext.not_three_dvd_fixed_involution_centralizer
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5) (hAP : A ≤ ctx.second)
    (hN : normalizer (A : Set G) ≤ ctx.second)
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (y : G) (hy : y ∈ centralizer (A : Set G)) (hy2 : orderOf y = 2) :
    ¬ 3 ∣ Nat.card (centralizer ({y} : Set G)) := by
  intro h3
  obtain ⟨T, hT, hTne, hTC, hAT, hfixed⟩ :=
    ctx.exists_three_subgroup_of_three_dvd_fixed_involution_centralizer
      hS A hA hN y hy hy2 h3
  exact hTne (ctx.three_subgroup_eq_bot_of_five_fixed_four
    hS A hA hAP hN hcard y hy hy2 T hT hTC hAT hfixed)

/-- The conditional odd-local exclusion in the four-fixed terminal alternative.
The additional noncyclicity and residual hypotheses of that alternative are
unnecessary: the fixed subgroup cardinality and normalizer confinement suffice. -/
public theorem LargeTerminalContext.not_fifteen_dvd_fixed_involution_centralizer
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5) (hAP : A ≤ ctx.second)
    (hN : normalizer (A : Set G) ≤ ctx.second)
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (y : G) (hy : y ∈ centralizer (A : Set G)) (hy2 : orderOf y = 2) :
    ¬ 15 ∣ Nat.card (centralizer ({y} : Set G)) := by
  intro h15
  exact ctx.not_three_dvd_fixed_involution_centralizer hS A hA hAP hN hcard y hy hy2
    ((by decide : 3 ∣ 15).trans h15)

end Stellmacher.Recognition
