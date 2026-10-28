module

public import Stellmacher.Recognition.MinimalSimpleOddCoreOvergroups
public import Stellmacher.Recognition.MinimalSimpleOddCoreInternalRankTwo
public import Stellmacher.Recognition.OddCoreQuotientControl
public import Stellmacher.Recognition.OddCoreSylow
public import Theory.GroupTheory.SolvableFourNormalizerSupplement
public import Theory.GroupTheory.RankTwoNormalAbelian

/-!
# Internal control through the rank-two quotient obstruction

Let M be a proper overgroup of the normalizer of a completed rank-three
odd-core closure R. Minimal simplicity makes M solvable. Its odd core and
the chosen ambient Sylow two-subgroup normalize R. If M fails to normalize R,
the two-core of M/O₂′(M) is self-centralizing and has elementary rank exactly
two. The quotient has no normal four-group, and every characteristic abelian
subgroup of its two-core is cyclic.

Internal normalizer control reduces to this specific quotient case, which
ambient involution fusion excludes in `MinimalSimpleOddCoreInternalRankTwo`.
The control theorem assembles these results for every small-rank two-subgroup
normalizer contained in M. In fact, the same exclusion shows that every proper
overgroup of the closure normalizer equals that normalizer. The conditional
assembly interface is retained. Solvability alone does not imply conjugation invariance of a
rank-three elementary commuting component; the ambient fusion input is essential.

Source: GLS2, Chapter F, Sections 19 and 21–22. The quotient reductions use
coprime component transport and the self-centralizing Fitting subgroup of a
solvable group. No global connectivity or weak-core control is assumed.
The rank-two exclusion proves the local weak-core fusion input from the N₂
theorem; it does not assume that input as an additional hypothesis.
-/

namespace Stellmacher.Recognition

/-- The odd core of an overgroup and the chosen Sylow subgroup together
normalize the completed closure. -/
public theorem minimalSimple_oddCore_internal_generated_control
    {G : Type*} [Group G] [Finite G] (hG : IsMinimalSimple G)
    (A M : Subgroup G) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (S : Sylow 2 G) (hAS : A ≤ S) (hM : M < ⊤)
    (hNM : Subgroup.normalizer (involutionOddCoreClosure A : Set G) ≤ M) :
    (pPrimeCore 2 M).map M.subtype ⊔ (S : Subgroup G) ≤
      Subgroup.normalizer (involutionOddCoreClosure A : Set G) :=
  sup_le (minimalSimple_oddCore_overgroup_sandwich hG A M hA hM hNM).2
    (sylow_le_normalizer_oddCoreClosure hG.isNTwoGroup S A hAS hA)

/-- Failure of control in a proper overgroup forces a self-centralizing
two-core of elementary rank exactly two in its odd-core quotient. -/
public theorem minimalSimple_oddCore_internal_quotient_obstruction
    {G : Type*} [Group G] [Finite G] (hG : IsMinimalSimple G)
    (A M : Subgroup G) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (hM : M < ⊤)
    (hNM : Subgroup.normalizer (involutionOddCoreClosure A : Set G) ≤ M)
    (hnot : ¬ M ≤ Subgroup.normalizer (involutionOddCoreClosure A : Set G)) :
    let X := M ⧸ pPrimeCore 2 M
    Group.IsSolvable X ∧ pPrimeCore 2 X = ⊥ ∧
      Subgroup.centralizer (pCore 2 X : Set X) ≤ pCore 2 X ∧
      (∃ D : Subgroup X, D ≤ pCore 2 X ∧ IsElementaryAbelian 2 D ∧ Nat.card D = 4) ∧
      (∀ D : Subgroup X, IsElementaryAbelian 2 D → D ≤ pCore 2 X → Nat.card D < 8) ∧
      (∀ U : Subgroup X, U.Normal → IsElementaryAbelian 2 U → Nat.card U ≠ 4) ∧
      ∀ B : Subgroup (pCore 2 X), B.Characteristic → IsMulCommutative B → IsCyclic B := by
  let X := M ⧸ pPrimeCore 2 M
  let : Group.IsSolvable M := hG.solvable_of_lt M hM
  have hAM : A ≤ M := (involutionOddCoreClosure_complete hG.isNTwoGroup A hA).2.2.1.trans hNM
  have hodd : pPrimeCore 2 X = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have hsmall : ∀ D : Subgroup X, IsElementaryAbelian 2 D →
      D ≤ pCore 2 X → Nat.card D < 8 := by
    intro D hD hDQ
    let : IsElementaryAbelian 2 D := hD
    exact card_lt_eight_of_not_le_oddCoreClosure_normalizer hG.isNTwoGroup A M
      hA hAM (pPrimeCore 2 M) (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
      hnot (pCore 2 X) D pCore_isPGroup hDQ
  have hno : ∀ U : Subgroup X, U.Normal → IsElementaryAbelian 2 U → Nat.card U ≠ 4 := by
    intro U hUn hUe hUcard
    let : U.Normal := hUn
    let : IsElementaryAbelian 2 U := hUe
    exact hnot (le_oddCoreClosure_normalizer_of_normal_four_odd_quotient hG.isNTwoGroup
      A M hA hAM (pPrimeCore 2 M) (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
      U hUcard)
  refine ⟨inferInstance, hodd, ?_, ?_, hsmall, hno, ?_⟩
  · rw [← Fitting_eq_pcore X 2 hodd]
    exact centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable inferInstance
  · let : IsElementaryAbelian 2 (A.subgroupOf M) := IsElementaryAbelian.subgroupOf hAM
    apply exists_elementary_four_le_pCore_odd_quotient_of_solvable (A.subgroupOf M)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv]
  · intro B hBc hBa
    let : B.Characteristic := hBc
    let : IsMulCommutative B := hBa
    exact Subgroup.isCyclic_characteristic_abelian_of_no_normal_four
      (pCore 2 X) pCore_isPGroup hsmall hno B

/-- Assembly of internal control once the remaining rank-two quotient case
has been proved. All other odd-quotient cases are handled by component transport. -/
public theorem minimalSimple_oddCore_internal_control_of_rank_two_input
    {G : Type*} [Group G] [Finite G] (hG : IsMinimalSimple G)
    (A M Q : Subgroup G) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (hM : IsCoatom M)
    (hNM : Subgroup.normalizer (involutionOddCoreClosure A : Set G) ≤ M)
    (hQM : Subgroup.normalizer (Q : Set G) ≤ M)
    (hresidual :
      (∀ D : Subgroup (M ⧸ pPrimeCore 2 M), IsElementaryAbelian 2 D →
        D ≤ pCore 2 (M ⧸ pPrimeCore 2 M) → Nat.card D < 8) →
      (∀ U : Subgroup (M ⧸ pPrimeCore 2 M), U.Normal →
        IsElementaryAbelian 2 U → Nat.card U ≠ 4) →
      Subgroup.normalizer (Q : Set G) ≤
        Subgroup.normalizer (involutionOddCoreClosure A : Set G)) :
    Subgroup.normalizer (Q : Set G) ≤
      Subgroup.normalizer (involutionOddCoreClosure A : Set G) := by
  by_cases hcontrol : M ≤ Subgroup.normalizer (involutionOddCoreClosure A : Set G)
  · exact hQM.trans hcontrol
  · obtain ⟨-, -, -, -, hsmall, hno, -⟩ :=
      minimalSimple_oddCore_internal_quotient_obstruction hG A M hA
        (lt_top_iff_ne_top.mpr hM.ne_top) hNM hcontrol
    exact hresidual hsmall hno

/-- A small-rank two-subgroup normalizer contained in a maximal overgroup
of the completed odd-core normalizer already normalizes the closure.
The rank-two quotient obstruction is excluded by ambient involution fusion. -/
public theorem minimalSimple_oddCore_internal_control
    {G : Type*} [Group G] [Finite G] (hG : IsMinimalSimple G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (hR : involutionOddCoreClosure A ≠ ⊥) (S : Sylow 2 G) (hAS : A ≤ S)
    (Q : Subgroup G) (hQ : Q ≠ ⊥) (hQtwo : IsPGroup 2 Q) (hQS : Q ≤ S)
    (hQsmall : ∀ B : Subgroup G, B ≤ Q → IsElementaryAbelian 2 B → Nat.card B < 8)
    (M : Subgroup G) (hM : IsCoatom M)
    (hNM : Subgroup.normalizer (involutionOddCoreClosure A : Set G) ≤ M)
    (hQM : Subgroup.normalizer (Q : Set G) ≤ M) :
    Subgroup.normalizer (Q : Set G) ≤
      Subgroup.normalizer (involutionOddCoreClosure A : Set G) :=
  minimalSimple_oddCore_internal_control_of_rank_two_input hG A M Q hA hM hNM hQM
    (minimalSimple_oddCore_internal_rank_two_control hG A hA hR S hAS
      Q hQ hQtwo hQS hQsmall M hM hNM hQM)

/-- Every proper overgroup of the completed closure normalizer is that
normalizer. The quotient obstruction and ambient fusion exclusion supply
the reverse containment; the odd-core sandwich alone would not suffice. -/
public theorem minimalSimple_oddCore_proper_overgroup_eq_normalizer
    {G : Type*} [Group G] [Finite G] (hG : IsMinimalSimple G)
    (A M : Subgroup G) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (hM : M < ⊤)
    (hNM : Subgroup.normalizer (involutionOddCoreClosure A : Set G) ≤ M) :
    M = Subgroup.normalizer (involutionOddCoreClosure A : Set G) := by
  apply le_antisymm _ hNM
  by_contra hnot
  obtain ⟨S, hAS⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨-, -, -, -, hsmall, hno, -⟩ :=
    minimalSimple_oddCore_internal_quotient_obstruction hG A M hA hM hNM hnot
  exact minimalSimple_oddCore_internal_rank_two_exclusion hG A M hA S hAS
    hM hNM hsmall hno

end Stellmacher.Recognition
