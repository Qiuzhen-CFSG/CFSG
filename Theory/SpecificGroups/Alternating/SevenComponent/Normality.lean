module
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy
public import Theory.GroupTheory.GeneralizedFitting.ComponentPrimeRankNormal
public import Theory.SpecificGroups.Alternating.TwoThreeCycles
public import Theory.Quasithin.CoprimeRank

/-!
# Normality of an A₇ C-component at three-rank at most two

The component modulo the ambient two-core is the actual simple A₇ quotient.
Distinct conjugates would give two commuting disjoint elementary nines,
contradicting the three-rank bound. Normality then reflects through the
solvable two-core. This supplies the normality step in Aschbacher–Smith
C.1.29, printed p.134, using only the stated local rank hypotheses.
-/
public section
open Subgroup Theory.GroupTheory
namespace alternatingGroup.SevenComponent

private theorem a7_quasisimple : IsQuasisimple (alternatingGroup (Fin 7)) where
  toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  simple := by
    let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
    exact ((QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup

theorem normal_of_core_quotient
    {G : Type*} [Group G] [Finite G] {K : Subgroup G}
    (hK : K.IsCComponent) (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (hr : primeRank 3 G ≤ 2) : K.Normal := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : IsQuasisimple (alternatingGroup (Fin 7)) := a7_quasisimple
  let q := QuotientGroup.mk' (pCore 2 G)
  let D := K.map q
  let eD : D ≃* alternatingGroup (Fin 7) :=
    (cComponentTwoCoreQuotientEquiv hK).symm.trans e
  have hD : IsComponent (G ⧸ pCore 2 G) D :=
    ⟨hK.subnormal.quotient, IsQuasisimple.of_mulEquiv eD.symm⟩
  have hz : center D = ⊥ := by
    apply eq_bot_iff.mpr
    intro z hz
    have he := (centerCongr eD ⟨z, hz⟩).property
    change eD z ∈ center (alternatingGroup (Fin 7)) at he
    rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at he
    exact eD.map_eq_one_iff.mp he
  have hDthree : 2 ≤ primeRank 3 D := by
    rw [primeRank_congr 3 eD]
    exact alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide)
  have hQthree : primeRank 3 (G ⧸ pCore 2 G) ≤ 2 := by
    rw [primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 G) pCore_isPGroup]
    exact hr
  have hn := hD.normal_of_centerless_of_primeRank hz 3 (by omega)
  let : Group.IsNilpotent (pCore 2 G) := pCore_isPGroup.isNilpotent
  exact cComponent_normal_of_quotient_normal hK (pCore 2 G) hn

/-- The same conclusion starts from literal subnormality and two-perfection;
C-component membership follows from the actual quasisimple two-core quotient. -/
theorem normal_of_twoPerfect_core_quotient
    {G : Type*} [Group G] [Finite G] {K : Subgroup G}
    (hK : K.IsSubnormal) (hp : IsPPerfect 2 K)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (hr : primeRank 3 G ≤ 2) : K.Normal := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsQuasisimple (alternatingGroup (Fin 7)) := a7_quasisimple
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv e.symm
  exact normal_of_core_quotient
    (isCComponent_of_isPPerfect_of_quasisimple_core_quotient hK hp) e hr
end alternatingGroup.SevenComponent
