module

public import Stellmacher.Recognition.MinimalSimpleBasic
public import Stellmacher.Recognition.OddCoreSolvableOvergroup
public import Theory.GroupTheory.Fitting.Subgroup
public import Mathlib.Order.Atoms.Finite

/-!
# Solvable maximal overgroups in the minimal-simple odd-core argument

Let R be the completed closure of a rank-three elementary binary subgroup.
For every proper overgroup M of N_G(R), minimal simplicity makes M solvable.
Local odd-core absorption and coprime component control then give
R ≤ O₂′(M) ≤ N_G(R). The two-core of M centralizes R, so F(M) ≤ N_G(R).
If R is nontrivial, N_G(R) is proper and has an actual maximal overgroup
with these properties. Equality of that overgroup with N_G(R) is not asserted.

These are inputs to the Bender method in GLS2, Chapter F, §19, combined with
the odd-core signalizer and connectivity results of §§21–22.
-/

namespace Stellmacher.Recognition

universe u

/-- The odd core of every proper overgroup of the closure normalizer lies
back in that normalizer, and contains the closure. This uses solvability of
arbitrary proper subgroups, rather than just solvability of two-locals. -/
public theorem minimalSimple_oddCore_overgroup_sandwich
    {G : Type u} [Group G] [Finite G] (hG : IsMinimalSimple G)
    (A M : Subgroup G) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (hM : M < ⊤)
    (hNM : Subgroup.normalizer (involutionOddCoreClosure A : Set G) ≤ M) :
    involutionOddCoreClosure A ≤ (pPrimeCore 2 M).map M.subtype ∧
      (pPrimeCore 2 M).map M.subtype ≤
        Subgroup.normalizer (involutionOddCoreClosure A : Set G) := by
  have hAM : A ≤ M := (involutionOddCoreClosure_complete hG.isNTwoGroup A hA).2.2.1.trans hNM
  refine ⟨oddCoreClosure_le_oddCore_of_solvable_overgroup A M
    (hG.solvable_of_lt M hM) hAM ((involutionOddCoreClosure A).le_normalizer.trans hNM), ?_⟩
  apply odd_le_normalizer_oddCoreClosure_of_normalized hG.isNTwoGroup A _ hA
  · rw [Subgroup.card_map_of_injective M.subtype_injective]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  · have hnorm : M ≤ Subgroup.normalizer ((pPrimeCore 2 M).map M.subtype : Set G) := by
      simpa only [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype] using (pPrimeCore 2 M).le_normalizer_map M.subtype
    exact hAM.trans hnorm

/-- The two-core of a proper overgroup centralizes the closure, and its
whole Fitting subgroup normalizes the closure. -/
public theorem minimalSimple_oddCore_overgroup_fitting
    {G : Type u} [Group G] [Finite G] (hG : IsMinimalSimple G)
    (A M : Subgroup G) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (hM : M < ⊤)
    (hNM : Subgroup.normalizer (involutionOddCoreClosure A : Set G) ≤ M) :
    (pCore 2 M).map M.subtype ≤
        Subgroup.centralizer (involutionOddCoreClosure A : Set G) ∧
      fittingSubgroupOf M ≤
        Subgroup.normalizer (involutionOddCoreClosure A : Set G) := by
  obtain ⟨hRcore, hcoreN⟩ := minimalSimple_oddCore_overgroup_sandwich hG A M hA hM hNM
  have htwoC : (pCore 2 M).map M.subtype ≤
      Subgroup.centralizer (involutionOddCoreClosure A : Set G) :=
    Subgroup.le_centralizer_iff.mp
      (hRcore.trans (pPrimeCore_map_le_centralizer_pCore_map (p := 2) M))
  refine ⟨htwoC, ?_⟩
  have hfit : fittingSubgroup M ≤ pCore 2 M ⊔ pPrimeCore 2 M := by
    rw [fitting_eq_sup_pCore]
    refine iSup_le fun q => ?_
    have hq : q.val.val.Prime := Nat.prime_of_mem_primeFactors q.val.property
    let : Fact q.val.val.Prime := ⟨hq⟩
    by_cases hq2 : q.val.val = 2
    · simpa only [hq2] using (le_sup_left : pCore 2 M ≤ pCore 2 M ⊔ pPrimeCore 2 M)
    · apply le_trans ?_ le_sup_right
      apply le_sSup
      refine ⟨inferInstance, ?_⟩
      obtain ⟨n, hn⟩ := (pCore_isPGroup (p := q.val.val) (G := M)).exists_card_eq
      rw [hn]
      exact ((Nat.coprime_primes Nat.prime_two hq).mpr (Ne.symm hq2)).pow_right n
  exact (Subgroup.map_mono (f := M.subtype) hfit).trans (by
    rw [Subgroup.map_sup]
    exact sup_le (htwoC.trans (Subgroup.centralizer_le_normalizer _)) hcoreN)

/-- There is an actual maximal solvable overgroup with the odd-core sandwich
and Fitting containment. No equality with the closure normalizer is assumed. -/
public theorem minimalSimple_oddCore_maximal_overgroup
    {G : Type u} [Group G] [Finite G] (hG : IsMinimalSimple G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (hR : involutionOddCoreClosure A ≠ ⊥) :
    ∃ M : Subgroup G, IsCoatom M ∧ Group.IsSolvable M ∧
      Subgroup.normalizer (involutionOddCoreClosure A : Set G) ≤ M ∧
      involutionOddCoreClosure A ≤ (pPrimeCore 2 M).map M.subtype ∧
      (pPrimeCore 2 M).map M.subtype ≤
        Subgroup.normalizer (involutionOddCoreClosure A : Set G) ∧
      fittingSubgroupOf M ≤
        Subgroup.normalizer (involutionOddCoreClosure A : Set G) := by
  let _ := hG.isSimpleGroup
  have hproper := (oddCore_component_normalizer
    hG.not_isSolvable hG.isNTwoGroup A hA hR).1
  obtain ⟨M, hM, hNM⟩ :=
    (eq_top_or_exists_le_coatom _).resolve_left (ne_of_lt hproper)
  have hlt : M < ⊤ := lt_top_iff_ne_top.mpr hM.ne_top
  obtain ⟨hRO, hON⟩ := minimalSimple_oddCore_overgroup_sandwich hG A M hA hlt hNM
  exact ⟨M, hM, hG.solvable_of_lt M hlt, hNM, hRO, hON,
    (minimalSimple_oddCore_overgroup_fitting hG A M hA hlt hNM).2⟩

end Stellmacher.Recognition
