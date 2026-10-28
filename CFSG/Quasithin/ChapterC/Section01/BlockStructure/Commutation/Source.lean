module
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Commutation.Cubic.CoreUniqueness
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Commutation.Cubic.ConjugateOrbit
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Commutation
public import Theory.GroupTheory.SelfCentralizingCoreInheritance
/-!
# C.1.9: distinct blocks commute

For cubic blocks in a group of characteristic two, induct on the ambient
order. Every proper subnormal block lies in a proper normal subgroup. Its
conjugates under the other cubic block lie there too, and characteristic two
is inherited. Induction makes distinct conjugates commute; the three-support
orbit bound then proves normalization. The proved normalizing dichotomy and
guarded core uniqueness give commutation. For the original hypothesis,
restrict both cubic blocks to O₂,₃(G). The existing quasisimple and mixed
branches complete the theorem. No normalization or core identity is assumed.

Source: Aschbacher–Smith, C.1.9, printed p.123, citing Aschbacher (1981),
Section 3.4. The extra upper-core hypothesis is essential: distinct normal
A₄ graphs in A₄ × C₃ share a four-group core and do not commute.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BlockCommutation
universe u

private theorem quotient_card_transport {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (h : Nat.card (A ⧸ pCore 2 A) = 3) :
    Nat.card (B ⧸ pCore 2 B) = 3 := by
  let q := QuotientGroup.congr (pCore 2 A) (pCore 2 B) e (pCore_map_iso 2 e)
  exact (Nat.card_congr q.toEquiv).symm.trans h

private theorem block_restrict {G : Type*} [Group G] [Finite G]
    {X N : Subgroup G} (hX : IsBlock X) (hXN : X ≤ N) : IsBlock (X.subgroupOf N) :=
  ⟨inferInstance,hX.short.of_mulEquiv (subgroupOfEquivOfLe hXN).symm,hX.subnormal.subgroupOf⟩

private theorem char_two_guard {G : Type*} [Group G] [Finite G]
    (hc : centralizer (pCore 2 G : Set G) ≤ pCore 2 G) : BlockCommutationHypothesis G := by
  intro _
  let N := upperTwoThreeCore G
  let : N.Normal := inferInstanceAs
    ((pCore 3 (G ⧸ pCore 2 G)).comap (QuotientGroup.mk' (pCore 2 G))).Normal
  exact generalizedFitting_eq_pCore_of_selfCentralizing 2 (normal_core_selfCentralizing hc N)

private theorem cubic_commutation_by_order (n : ℕ) :
    ∀ (G : Type u) [Group G] [Finite G], Nat.card G = n →
      (centralizer (pCore 2 G : Set G) ≤ pCore 2 G) →
      ∀ X Y : Subgroup G, IsBlock X → IsBlock Y →
        Nat.card (X ⧸ pCore 2 X) = 3 → Nat.card (Y ⧸ pCore 2 Y) = 3 →
        X ≠ Y → ⁅X,Y⁆ = ⊥ := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro G _ _ hcard hself X Y hX hY hqX hqY hne
    have hnorm (A B : Subgroup G) (hA : IsBlock A) (hB : IsBlock B)
        (hqA : Nat.card (A ⧸ pCore 2 A) = 3)
        (hqB : Nat.card (B ⧸ pCore 2 B) = 3) : B ≤ normalizer (A : Set G) := by
      by_cases he : A = ⊤
      · rw [he,normalizer_eq_top]
        exact le_top
      obtain ⟨N,hN,hAN,hNtop⟩ := hA.subnormal.exists_normal_and_le_and_lt_top_of_ne he
      let := hN
      have hNcard : Nat.card N < n := by
        rw [← hcard]
        have hlt := Set.Finite.card_lt_card (Set.toFinite ((⊤ : Subgroup G) : Set G))
          (show (N : Set G) ⊂ ((⊤ : Subgroup G) : Set G) from hNtop)
        change Nat.card N < Nat.card (⊤ : Subgroup G) at hlt
        simpa only [card_top] using hlt
      apply cubic_actor_normalizes_of_conjugates_commute hA hB hqA hqB
      intro a b hab
      let A₁ := A.conjBy (a : G)
      let A₂ := A.conjBy (b : G)
      have h₁ : IsBlock A₁ := hA.map_equiv (MulAut.conj (a : G))
      have h₂ : IsBlock A₂ := hA.map_equiv (MulAut.conj (b : G))
      have hn₁ : A₁ ≤ N := by
        rintro x ⟨z,hz,rfl⟩
        exact hN.conj_mem z (hAN hz) a
      have hn₂ : A₂ ≤ N := by
        rintro x ⟨z,hz,rfl⟩
        exact hN.conj_mem z (hAN hz) b
      have hneq : A₁.subgroupOf N ≠ A₂.subgroupOf N := by
        intro hh
        have hh := congrArg (Subgroup.map N.subtype) hh
        rw [map_subgroupOf_eq_of_le hn₁,map_subgroupOf_eq_of_le hn₂] at hh
        exact hab hh
      have hq₁ := quotient_card_transport ((MulAut.conj (a : G)).subgroupMap A) hqA
      have hq₂ := quotient_card_transport ((MulAut.conj (b : G)).subgroupMap A) hqA
      have hcomm := ih (Nat.card N) hNcard N rfl (normal_core_selfCentralizing hself N)
        (A₁.subgroupOf N) (A₂.subgroupOf N) (block_restrict h₁ hn₁) (block_restrict h₂ hn₂)
        (quotient_card_transport (subgroupOfEquivOfLe hn₁).symm hq₁)
        (quotient_card_transport (subgroupOfEquivOfLe hn₂).symm hq₂) hneq
      have hh := congrArg (Subgroup.map N.subtype) hcomm
      rwa [map_commutator,map_subgroupOf_eq_of_le hn₁,map_subgroupOf_eq_of_le hn₂,Subgroup.map_bot] at hh
    exact cubic_blocks_commute_of_normalizes X Y hX hY hqX hqY (char_two_guard hself) hne
      (hnorm X Y hX hY hqX hqY) (hnorm Y X hY hX hqY hqX)

/-- Cubic blocks commute in a finite group of characteristic two. -/
theorem cubic_blocks_commute_of_selfCentralizing {G : Type u} [Group G] [Finite G]
    (hc : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (X Y : Subgroup G) (hX : IsBlock X) (hY : IsBlock Y)
    (hqX : Nat.card (X ⧸ pCore 2 X) = 3) (hqY : Nat.card (Y ⧸ pCore 2 Y) = 3)
    (hne : X ≠ Y) : ⁅X,Y⁆ = ⊥ :=
  cubic_commutation_by_order (Nat.card G) G rfl hc X Y hX hY hqX hqY hne

/-- The complete cubic case under the original upper-core guard of C.1.9. -/
theorem cubic_blocks_commute {G : Type u} [Group G] [Finite G]
    (X Y : Subgroup G) (hX : IsBlock X) (hY : IsBlock Y)
    (hqX : Nat.card (X ⧸ pCore 2 X) = 3) (hqY : Nat.card (Y ⧸ pCore 2 Y) = 3)
    (hG : BlockCommutationHypothesis G) (hne : X ≠ Y) : ⁅X,Y⁆ = ⊥ := by
  let H := upperTwoThreeCore G
  have hXH : X ≤ H := hX.le_upperTwoThreeCore_of_quotient_three hqX
  have hYH : Y ≤ H := hY.le_upperTwoThreeCore_of_quotient_three hqY
  have hfit := hG.fitting_of_quotient_three hX hqX
  have hself : centralizer (pCore 2 H : Set H) ≤ pCore 2 H := by
    rw [← hfit]
    exact centralizer_generalizedFitting_le H
  have hneq : X.subgroupOf H ≠ Y.subgroupOf H := by
    intro hh
    have hh := congrArg (Subgroup.map H.subtype) hh
    rw [map_subgroupOf_eq_of_le hXH,map_subgroupOf_eq_of_le hYH] at hh
    exact hne hh
  have hcomm := cubic_blocks_commute_of_selfCentralizing hself
    (X.subgroupOf H) (Y.subgroupOf H) (block_restrict hX hXH) (block_restrict hY hYH)
    (quotient_card_transport (subgroupOfEquivOfLe hXH).symm hqX)
    (quotient_card_transport (subgroupOfEquivOfLe hYH).symm hqY) hneq
  have hh := congrArg (Subgroup.map H.subtype) hcomm
  rwa [map_commutator,map_subgroupOf_eq_of_le hXH,map_subgroupOf_eq_of_le hYH,Subgroup.map_bot] at hh

end CFSG.Quasithin.ChapterC.BlockCommutation
namespace CFSG.Quasithin.ChapterC
universe u
/-- C.1.9: distinct blocks commute, with the published alternating-three guard. -/
theorem blocks_commute {G : Type u} [Group G] [Finite G]
    (hG : BlockCommutationHypothesis G) {X Y : Subgroup G}
    (hX : IsBlock X) (hY : IsBlock Y) (hne : X ≠ Y) : ⁅X,Y⁆ = ⊥ :=
  blocks_commute_of_cubic_case BlockCommutation.cubic_blocks_commute hG hX hY hne
end CFSG.Quasithin.ChapterC
