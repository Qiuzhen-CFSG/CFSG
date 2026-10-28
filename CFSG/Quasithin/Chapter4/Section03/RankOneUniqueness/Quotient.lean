module
public import Theory.SpecificGroups.SL2.BinaryOddRank
public import Theory.SpecificGroups.SL2.SylowUniqueMaximal
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import Theory.GroupTheory.UniqueMaximalNormalExtension
public import CFSG.Quasithin.ClassicalModels
public import Theory.PGroupCore
public import Theory.Quasithin.CoprimeRank
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# The two-core quotient calculations for rank-one uniqueness

The actual PSL₂ quotient in characteristic two is SL₂. Its odd-prime rank
is at most one and every defining-characteristic Sylow has a unique
maximal overgroup. These properties lift through the literal two-core map.
Source application: Aschbacher--Smith 4.3.1, printed p.613.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
variable {E : Type*} [Group E] [Finite E] {n : ℕ}

/-- Odd-prime rank is unchanged by the literal two-core quotient. -/
theorem odd_primeRank_le_one
    (hpsl : ClassicalGroup.IsPSL (E ⧸ pCore 2 E) 2 (2 ^ n))
    {p : ℕ} [Fact p.Prime] (ho : Odd p) : primeRank p E ≤ 1 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hpsl
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  let e' := e.trans (Theory.PSL2.sl2QuotientEquiv F).symm
  rw [← primeRank_quotient_eq_of_isTwoGroup p ho (pCore 2 E) pCore_isPGroup,
    primeRank_congr p e']
  exact Matrix.SL2.binary_odd_primeRank_le_one ho

/-- Lift the actual rank-one Borel property through O₂(E). -/
theorem sylow_hasUniqueMaximalOver
    (hpsl : ClassicalGroup.IsPSL (E ⧸ pCore 2 E) 2 (2 ^ n)) (S : Sylow 2 E) :
    Order.HasUniqueMaximalOver (S : Subgroup E) ⊤ := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hpsl
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  let e' := e.trans (Theory.PSL2.sl2QuotientEquiv F).symm
  let q := e'.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 E))
  have hq : Function.Surjective q := e'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 E := by
    ext x
    exact e'.map_eq_one_iff.trans (QuotientGroup.eq_one_iff _)
  apply hasUniqueMaximalOver_of_surjective q hq
  · rw [hk]
    exact pCore_isPGroup.le_sylow_of_normal S
  · exact Matrix.SpecialLinearGroup.sylow_hasUniqueMaximalOver 2 (S.mapSurjective hq)
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
