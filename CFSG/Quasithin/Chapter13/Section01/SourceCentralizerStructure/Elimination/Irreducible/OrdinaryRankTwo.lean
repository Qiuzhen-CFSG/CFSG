module
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Irreducible.CharacteristicTwo.G2
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Irreducible.OrdinaryPair

/-!
# Ordinary central quotients and the symplectic and G₂ exclusions

For an ordinary escaping component the center equals its two-core. Thus the
actual two-core quotient is simple and centerless. This supplies both kernel
bounds required by the stabilizer-action exclusions, without the C.2.7 star
model. For simple whole-component models the two-core quotient is identified
with K only after proving its center trivial. Every model equivalence below
passes through these explicit quotient comparisons.

Source: Aschbacher–Smith, 13.1.12(3), printed p.875.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
open Chapter1 Chapter1.XiEmbedding.InvariantLarge ClassificationModels
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L : Subgroup G} {p : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
/-- Simplicity belongs to the actual two-core quotient of the ordinary component. -/
theorem Escape.ordinary_quotient_simple {u : G} {K : Subgroup G}
    (e : Escape T L p u K) (hq : IsQuasisimple K) : IsSimpleGroup (XiQuotient K) := by
  let := hq
  let : IsSimpleGroup (K ⧸ center K) := hq.simple
  exact (QuotientGroup.quotientMulEquivOfEq (e.ordinary_center hq)).symm.isSimpleGroup

omit [Fact p.Prime] in
/-- Perfectness makes the central quotient centerless; O₂(K)=Z(K) identifies it. -/
theorem Escape.ordinary_quotient_center {u : G} {K : Subgroup G}
    (e : Escape T L p u K) (hq : IsQuasisimple K) : center (XiQuotient K) = ⊥ := by
  let := hq
  let j : (K ⧸ center K) ≃* XiQuotient K :=
    QuotientGroup.quotientMulEquivOfEq (e.ordinary_center hq)
  apply bot_unique
  intro x hx
  have hxC := (centerCongr j.symm ⟨x,hx⟩).property
  have hx1 : j.symm x = 1 := (Group.IsPerfect.center_quotient_center_eq_bot K).le hxC
  exact mem_bot.mpr (j.symm.map_eq_one_iff.mp hx1)

omit [Fact p.Prime] in
/-- The whole component is recovered only in the simple ordinary case. -/
noncomputable def Escape.ordinary_simple_quotient_equiv {u : G} {K : Subgroup G}
    (e : Escape T L p u K) (hq : IsQuasisimple K) [IsSimpleGroup K] : XiQuotient K ≃* K := by
  let := hq
  have hz : center K = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (center K) inferInstance).resolve_right
      (fun hc => Group.IsPerfect.not_isMulCommutative K (center_eq_top_iff.mp hc))
  exact (QuotientGroup.quotientMulEquivOfEq ((e.ordinary_center hq).symm.trans hz)).trans
    QuotientGroup.quotientBot

/-- The existing G₂ stabilizer obstruction applies to the ordinary quotient,
including a nontrivial two-central cover of G₂(4). -/
theorem Context.not_ordinary_g2_quotient (h : Context T L p)
    {u : G} (s : Selected T L u) {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u) (hq : IsQuasisimple K)
    (hs : SymmetricThreeStabilizerQuotient L p u) {n : ℕ} (hn : 1 < n)
    (hm : IsG2At (XiQuotient K) (2^n)) : False := by
  obtain ⟨F,_,_,hF,⟨j⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  have hz := e.ordinary_quotient_center hq
  exact h.not_g2_model s e hi hs (by rw [hF]; exact
    (show 2^1 < 2^n from Nat.pow_lt_pow_right (by decide) hn))
    (by simp [hz]) (by simp [hz])
    (((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).trans j)

/-- A simple ordinary G₂ whole model supplies the actual quotient model. -/
theorem Context.not_ordinary_g2 (h : Context T L p)
    {u : G} (s : Selected T L u) {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u) (hq : IsQuasisimple K)
    [IsSimpleGroup K] (hs : SymmetricThreeStabilizerQuotient L p u)
    {n : ℕ} (hn : 1 < n) (hm : IsG2At K (2^n)) : False :=
  h.not_ordinary_g2_quotient s e hi hq hs hn
    (hm.of_mulEquiv (e.ordinary_simple_quotient_equiv hq))

/-- The ordinary PSp₄ model supplies the actual characteristic-two symplectic
carrier, with all quotient-center hypotheses discharged. -/
theorem Context.not_ordinary_symplectic (h : Context T L p)
    {u : G} (s : Selected T L u) {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u) (hq : IsQuasisimple K)
    [IsSimpleGroup K] (hs : SymmetricThreeStabilizerQuotient L p u)
    {n : ℕ} (hn : 1 < n) (hm : ClassicalGroup.IsPSp K 2 (2^n)) : False := by
  obtain ⟨F,_,_,hF,⟨j⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  have hz := e.ordinary_quotient_center hq
  let j' := ((e.ordinary_simple_quotient_equiv hq).trans j).trans
    Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm
  exact h.not_symplectic_model s e hi hs hF hn (by simp [hz]) (by simp [hz])
    (((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).trans j')

end CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
