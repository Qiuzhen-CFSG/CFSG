module
public import CFSG.Quasithin.ChapterC.Section02.SourceHypotheses
public import Theory.GroupTheory.CComponent.FullOddRankCharacteristic
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Theory.Alternating.PrimeRank

/-!
# Odd prime rank in the original C.2.8 conjugate span

A source component whose centerless quotient has the full positive odd
prime rank of its conjugate span is characteristic in that span. Its
local conjugators consequently normalize it. For an A₅ quotient this
says that a genuinely nonnormal source configuration has five-rank at
least two, without choosing or identifying its two conjugate factors.

Source: Aschbacher–Smith A.3.18 and C.4.8, specialized to the original
nonnormal A₅ covering configuration of 4.2.12–13, printed pp.610–611.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
universe u
variable {G : Type u} [Group G] [Finite G] {H M L R V : Subgroup G}
variable {κ : GroupClass.{u}}
/-- Full positive odd rank of the seed quotient forces local normality. -/
theorem normalizes_of_span_odd_rank
    (h : HypothesisC28 κ H M L R V)
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    [IsQuasisimple (L ⧸ pCore 2 L)] (hz : center (L ⧸ pCore 2 L) = ⊥)
    (hne : 0 < primeRank p (L ⧸ pCore 2 L))
    (hr : primeRank p (conjugateSpanBy L M) ≤ primeRank p (L ⧸ pCore 2 L)) :
    M ≤ normalizer (L : Set G) := by
  let X := conjugateSpanBy L M
  let A := L.subgroupOf X
  let a : A ≃* L := subgroupOfEquivOfLe (le_conjugateSpanBy L M)
  let e : A ⧸ pCore 2 A ≃* L ⧸ pCore 2 L :=
    QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let : IsQuasisimple (A ⧸ pCore 2 A) := IsQuasisimple.of_mulEquiv e.symm
  have hc : center (A ⧸ pCore 2 A) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have : e x = 1 := hz.le ((centerCongr e) ⟨x,hx⟩).property
    exact e.map_eq_one_iff.mp this
  have hA := h.component.subgroupOf_of_le (le_conjugateSpanBy L M)
    (conjugateSpanBy_le_self h.component_le)
  let : A.Characteristic := hA.characteristic_of_full_odd_rank hp hc
    (by rwa [primeRank_congr p e]) (by rwa [primeRank_congr p e])
  have hn := (le_normalizer_conjugateSpanBy L M).trans
    (normalizer_le_normalizer_characteristic_image X A)
  rwa [map_subgroupOf_eq_of_le (le_conjugateSpanBy L M)] at hn
/-- An A₅-marked source component is normalized when its span has five-rank at most one. -/
theorem normalizes_of_a5_span_fiveRank_le_one
    (h : HypothesisC28 κ H M L R V)
    (e : L ⧸ pCore 2 L ≃* alternatingGroup (Fin 5))
    (hr : primeRank 5 (conjugateSpanBy L M) ≤ 1) :
    M ≤ normalizer (L : Set G) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : IsQuasisimple (alternatingGroup (Fin 5)) := {
    toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    simple := by
      let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
      exact ((QuotientGroup.quotientMulEquivOfEq
        (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
  let : IsQuasisimple (L ⧸ pCore 2 L) := IsQuasisimple.of_mulEquiv e.symm
  have hz : center (L ⧸ pCore 2 L) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hx' : e x ∈ center (alternatingGroup (Fin 5)) := ((centerCongr e) ⟨x,hx⟩).property
    exact e.map_eq_one_iff.mp ((alternatingGroup.center_eq_bot (by simp)).le hx')
  have he : primeRank 5 (L ⧸ pCore 2 L) = 1 := by
    rw [primeRank_congr 5 e,
      GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime 5 5 (by decide) (by decide)]
  exact h.normalizes_of_span_odd_rank (by decide : Odd 5) hz (by omega) (by omega)

/-- The actual nonnormal A₅ source configuration has five-rank at least two. -/
theorem two_le_span_fiveRank_of_a5_nonnormal
    (h : HypothesisC28 κ H M L R V)
    (e : L ⧸ pCore 2 L ≃* alternatingGroup (Fin 5))
    (hn : ¬ M ≤ normalizer (L : Set G)) :
    2 ≤ primeRank 5 (conjugateSpanBy L M) := by
  by_contra! hr
  exact hn (h.normalizes_of_a5_span_fiveRank_le_one e (by omega))

end CFSG.Quasithin.ChapterC.HypothesisC28
