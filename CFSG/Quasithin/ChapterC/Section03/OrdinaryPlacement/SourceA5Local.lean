module
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.SourceLocalQuotient
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.SpanOddRank
public import Theory.SpecificGroups.SymplecticFour.EvenProjective

/-!
# The ordinary binary local rows in the genuine nonnormal A₅ configuration

The original A₅-marked C-component has a conjugate span of five-rank at
least two. C.3.2–C.3.4 place that same span in the ordinary component,
normalizing its noncentral radical intersection. The literal local
quotient bounds for binary PSL₃, Sp₄ and G₂ contradict that rank.

Both coordinate equivalences and the actual Theorem C model predicates
are accepted. The original C.2.8 subgroups, radical and module are retained;
local normality is a conclusion, never an additional premise.

Source: Aschbacher–Smith C.3.5 and C.4.8, printed pp.150,153, in the
A₅ specialization of the covering argument of 4.2.12–13, pp.610–611.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G : Type*} [Group G] [Finite G] {H M L R V : Subgroup G}

/-- The binary symplectic ordinary row already forces the required local normality. -/
theorem normalizes_a5_of_ordinary_sp4
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* alternatingGroup (Fin 5))
    (K : Subgroup H) (hK : IsComponent H K)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : K ⧸ center K ≃* Theory.SpecificGroups.SymplecticFour.Sp F) :
    M ≤ normalizer (L : Set G) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact h.normalizes_of_a5_span_fiveRank_le_one a
    (h.ordinary_span_primeRank_le_one_of_sp4 K hK e (by decide))

/-- The binary G₂ ordinary row likewise forces local normality. -/
theorem normalizes_a5_of_ordinary_g2
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* alternatingGroup (Fin 5))
    (K : Subgroup H) (hK : IsComponent H K)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : K ⧸ center K ≃* Atlas.G2.Model F) (hq : 2 < Nat.card F) :
    M ≤ normalizer (L : Set G) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact h.normalizes_of_a5_span_fiveRank_le_one a
    (h.ordinary_span_primeRank_le_one_of_g2 K hK e hq (by decide))

/-- The binary projective degree-three ordinary row forces local normality. -/
theorem normalizes_a5_of_ordinary_psl3
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* alternatingGroup (Fin 5))
    (K : Subgroup H) (hK : IsComponent H K)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : K ⧸ center K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) :
    M ≤ normalizer (L : Set G) :=
  h.normalizes_of_a5_span_fiveRank_le_one a
    (h.ordinary_span_fiveRank_le_one_of_psl3 K hK e)

/-- The actual projective symplectic catalogue marking supplies the same conclusion. -/
theorem normalizes_a5_of_ordinary_isPSp
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* alternatingGroup (Fin 5))
    (K : Subgroup H) (hK : IsComponent H K) {n : ℕ}
    (hm : ClassicalGroup.IsPSp (K ⧸ center K) 2 (2 ^ n)) :
    M ≤ normalizer (L : Set G) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  exact h.normalizes_a5_of_ordinary_sp4 a K hK
    (e.trans (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := F)).symm)

/-- The actual G₂ catalogue marking supplies the same conclusion in its simple range. -/
theorem normalizes_a5_of_ordinary_isG2At
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* alternatingGroup (Fin 5))
    (K : Subgroup H) (hK : IsComponent H K) {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassificationModels.IsG2At (K ⧸ center K) (2 ^ n)) :
    M ≤ normalizer (L : Set G) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  apply h.normalizes_a5_of_ordinary_g2 a K hK e
  rw [hF]
  exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
    (Nat.pow_le_pow_right (by decide) hn)

/-- The actual degree-three projective catalogue marking supplies local normality. -/
theorem normalizes_a5_of_ordinary_isPSL3
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* alternatingGroup (Fin 5))
    (K : Subgroup H) (hK : IsComponent H K) {n : ℕ}
    (hm : ClassicalGroup.IsPSL (K ⧸ center K) 3 (2 ^ n)) :
    M ≤ normalizer (L : Set G) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  exact h.normalizes_a5_of_ordinary_psl3 a K hK e

/-- An ordinary central quotient of five-rank at most one cannot contain
the span of a nonnormal A₅-marked source component. -/
theorem normalizes_a5_of_ordinary_quotient_fiveRank_le_one
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* alternatingGroup (Fin 5))
    (K : Subgroup H) (hK : IsComponent H K)
    (hb : primeRank 5 (K ⧸ center K) ≤ 1) :
    M ≤ normalizer (L : Set G) := by
  obtain ⟨_,_,_,_,hr⟩ := h.ordinary_quotient_local_data K hK
  let A := (((conjugateSpanBy L M).subgroupOf H).subgroupOf K).map
    (QuotientGroup.mk' (center K))
  apply h.normalizes_of_a5_span_fiveRank_le_one a
  rw [←hr 5 (by decide) (by decide)]
  exact (Theory.GroupTheory.primeRank_le_of_injective 5 A.subtype A.subtype_injective).trans hb

/-- All alternating rows of Theorem C force local normality in the A₅ case. -/
theorem normalizes_a5_of_ordinary_alternating
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* alternatingGroup (Fin 5))
    (K : Subgroup H) (hK : IsComponent H K) {n : ℕ} (hn : n ≤ 8)
    (e : K ⧸ center K ≃* alternatingGroup (Fin n)) :
    M ≤ normalizer (L : Set G) := by
  apply h.normalizes_a5_of_ordinary_quotient_fiveRank_le_one a K hK
  rw [primeRank_congr 5 e,
    GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime n 5 (by decide) (by decide)]
  omega

end CFSG.Quasithin.ChapterC.HypothesisC28
