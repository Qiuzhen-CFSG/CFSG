module

public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.Source523
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.GlobalPrimes
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder
public import Theory.AtlasPort.LinearGroups.G2.Order
public import Theory.SpecificGroups.Triality.Model.QTKE
public import Theory.SpecificGroups.Triality.ConcreteBruhat.FixedCellCount
public import Theory.SpecificGroups.Tits.FiniteImageOrder
public import Theory.GroupTheory.SimpleSectionSolvableReduction

public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.SmallGlobal.UnitaryTwo

/-!
# Excluding the small-field global alternatives in 13.6.27

A finite simple group of order divisible by 35 cannot be a member of the
complete rank-two catalogue at field exponent at most one. The parameter
restrictions eliminate U₅, the ordinary symplectic and G₂ families, and Ree.
The remaining six carriers have the following order obstructions:

* PSL₃(2) has order 168, with no factor five.
* PSU₄(2) is a quotient of a subgroup of GU₄(2), whose order 77760 has no seven.
* The specified PSp₄(2) derived subgroup has order dividing 720, with no seven.
* The specified G₂(2) derived subgroup has order dividing 12096, with no five.
* Genuine triality ³D₄(2) has order 211341312, with no five, by its fixed cells.
* Simplicity inherited by Parrott's Tits carrier makes its certified nontrivial
  quotient map injective; the quotient order 17971200 has no seven.

Every step uses the actual catalogue equivalence and literal subgroup or
quotient map. In particular the triality carrier is the graph-field model,
and no independent simplicity theorem for the Tits presentation is required.

The final theorem applies the sieve to the literal component candidate in
C_G(z). Its order supplies both primes via `GlobalPrimes`. The M₂₃ and
larger-field ambient exclusions are the precise consequences of source
Hypothesis 13.3.1(2),(3); their discharge remains with the parent assembly,
as do component uniqueness and applicability of the earlier theorem.

Source: Aschbacher–Smith, combined manuscript, Theorem 5.2.3, printed
p.649/PDF666, and final component exclusion in 13.6.27, printed p.934/PDF951,
`refs/quasithin.pdf`. This is a conditional model sieve, not a proof of 5.2.3.
-/

open Subgroup
open CFSG.Quasithin.ClassificationModels

namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation

private theorem not_thirtyFive_dvd_of_linear_two {G : Type*} [Group G] (h : ClassicalGroup.IsPSL G 3 2) :
    ¬ 35 ∣ Nat.card G := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, Matrix.PSL3.LinearThree.card_projective, hF]
  decide

private theorem not_thirtyFive_dvd_of_symplectic_derived {G : Type*} [Group G]
    (h : Nonempty (G ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2)))) :
    ¬ 35 ∣ Nat.card G := by
  obtain ⟨e⟩ := h
  intro hd
  rw [Nat.card_congr e.toEquiv] at hd
  have hb := hd.trans ((commutator (ClassicalGroup.PSp 2 (ZMod 2))).card_subgroup_dvd_card.trans
    (center (Matrix.symplecticGroup (Fin 2) (ZMod 2))).card_quotient_dvd_card)
  rw [Theory.SpecificGroups.SymplecticFour.card_sp (ZMod 2)] at hb
  norm_num [Nat.card_zmod] at hb

private theorem not_thirtyFive_dvd_of_g2_derived {G : Type*} [Group G]
    (h : Nonempty (G ≃* commutator (Atlas.G2.Model (ZMod 2)))) :
    ¬ 35 ∣ Nat.card G := by
  obtain ⟨e⟩ := h
  intro hd
  rw [Nat.card_congr e.toEquiv] at hd
  have hb := hd.trans (commutator (Atlas.G2.Model (ZMod 2))).card_subgroup_dvd_card
  rw [Atlas.G2.card_Model] at hb
  norm_num [Nat.card_zmod] at hb

private theorem not_thirtyFive_dvd_of_triality_two {G : Type*} [Group G] (h : Triality.Standard.IsTrialityGroupAt 2 G) :
    ¬ 35 ∣ Nat.card G := by
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_two_iff G).mp h
  rw [Nat.card_congr e.toEquiv]
  rw [Triality.Standard.ConcreteBruhat.FixedCellCount.card_carrier,
    Triality.Standard.ConcreteBruhat.FixedCellCount.card_borel]
  norm_num [Triality.Standard.binaryParameters_q]

private theorem not_thirtyFive_dvd_of_tits {G : Type*} [Group G] [IsSimpleGroup G]
    (h : Nonempty (G ≃* Tits.ParrottGroup)) : ¬ 35 ∣ Nat.card G := by
  obtain ⟨e⟩ := h
  let : IsSimpleGroup Tits.ParrottGroup := e.isSimpleGroup_congr.mp inferInstance
  let : Nontrivial Tits.Atlas1600Group := Finite.one_lt_card_iff_nontrivial.mp
    (by rw [Tits.atlas1600Group_card]; decide)
  have hi := Tits.parrottFiniteImageMap.injective_of_surjective_of_simple
    Tits.parrottFiniteImageMap_surjective
  rw [Nat.card_congr e.toEquiv,
    Nat.card_congr (Equiv.ofBijective Tits.parrottFiniteImageMap
      ⟨hi, Tits.parrottFiniteImageMap_surjective⟩), Tits.atlas1600Group_card]
  decide

/-- The complete rank-two catalogue has no field-two endpoint whose order
is divisible by both five and seven. -/
public theorem rankTwo_parameter_gt_one_of_thirtyFive_dvd
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] {f : ℕ}
    (hm : IsRankTwoModel G f) (h35 : 35 ∣ Nat.card G) : 1 < f := by
  by_contra! hf
  cases hm with
  | linear hpos hi =>
    have he : f = 1 := by omega
    subst f
    exact not_thirtyFive_dvd_of_linear_two (by simpa only [pow_one] using hi) h35
  | unitary_four hpos hi =>
    have he : f = 1 := by omega
    subst f
    exact SmallGlobalUnitary.not_thirtyFive_dvd_of_unitary_two
      (by simpa only [pow_one] using hi) h35
  | unitary_five he hi => omega
  | symplectic hpos hi => omega
  | g2 hpos hi => omega
  | triality hpos hi =>
    have he : f = 1 := by omega
    subst f
    exact not_thirtyFive_dvd_of_triality_two (by simpa only [pow_one] using hi) h35
  | ree_f4 m hm he hi => omega
  | symplectic_derived he hi => exact not_thirtyFive_dvd_of_symplectic_derived hi h35
  | g2_derived he hi => exact not_thirtyFive_dvd_of_g2_derived hi h35
  | tits he hi => exact not_thirtyFive_dvd_of_tits hi h35

/-- The literal candidate in C_G(z) rules out both global alternatives of
5.2.3 under the two ambient exclusions from Hypothesis 13.3.1(2),(3).
Their source discharge, and the application of 5.2.3, belong to the parent. -/
public theorem not_globalAlternative_of_candidate
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (T : Sylow 2 G) (z : G) {K : Subgroup (centralizer ({z} : Set G))}
    (hc : Candidate ((T : Subgroup G).subgroupOf (centralizer ({z} : Set G))) K)
    (hM23 : ¬ Nonempty (G ≃* Sporadic.Mathieu.M23))
    (hlarge : ∀ f : ℕ, 1 < f → ¬ IsRankTwoModel G f) :
    ¬ Source523.GlobalAlternative G := by
  rintro (h | ⟨f, hm⟩)
  · exact hM23 h
  · exact hlarge f (rankTwo_parameter_gt_one_of_thirtyFive_dvd hm
      (centralizer_candidate_thirtyFive_dvd T z hc)) hm

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
