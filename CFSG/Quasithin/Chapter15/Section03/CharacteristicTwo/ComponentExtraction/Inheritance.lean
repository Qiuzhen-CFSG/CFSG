module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.ComponentExtraction.InternalModule
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Stellmacher.CharacteristicTwoCoreOvergroup
public import FeitThompson.BGsection1.CentralizerLemmas
public import Theory.GroupTheory.PCoreOvergroup

/-!
# Inheritance for minimal contrary outside overgroups

The centralizer criterion for characteristic two is equivalent to the genuine
`F* = O₂` equality: the odd core vanishes and each component lies in or
centralizes the two-core. Overgroups of the source Sylow subgroup inherit this
criterion and contain the original two-core. Finite minimization therefore
selects a member of the actual minimal outside family, still of characteristic
two, below any contrary overgroup.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), A.1.6,
1.1.4, and the minimal-overgroup reductions in 15.3, printed pp.1130–1134.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The self-centralizing two-core criterion recovers the actual generalized
Fitting equality, including the component-layer assertion. -/
theorem hasCharacteristicTwo_of_centralizer {I : Subgroup G}
    (hc : centralizer (pCore 2 I : Set I) ≤ pCore 2 I) : HasCharacteristicTwo I := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : pPrimeCore 2 I = ⊥ := by
    have hle : pPrimeCore 2 I ≤ pCore 2 I :=
      (pPrimeCore_le_centralizer_of_normal_pgroup 2 (pCore 2 I) pCore_isPGroup).trans hc
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := I)).exists_card_eq
    have hcop : Nat.Coprime (Nat.card (pCore 2 I)) (Nat.card (pPrimeCore 2 I)) := by
      rw [hn]
      exact (pPrimeCore_coprime_card (p := 2) (G := I)).pow_left n
    exact le_bot_iff.mp ((le_inf hle le_rfl).trans_eq
      (disjoint_of_coprime_natCard hcop).eq_bot)
  apply le_antisymm
  · change fittingSubgroup I ⊔ Theory.GroupTheory.componentLayer I ≤ pCore 2 I
    refine sup_le (Fitting_eq_pcore I 2 hodd).le ?_
    apply sSup_le
    intro L hL
    rcases hL.normal_dichotomy (pCore 2 I) with h | h
    · exact h
    · exact (commutator_eq_bot_iff_le_centralizer.mp h).trans hc
  · exact (pCore_le_fitting I 2).trans (Theory.GroupTheory.fitting_le_generalizedFitting I)

theorem hasCharacteristicTwo_iff_centralizer {I : Subgroup G} :
    HasCharacteristicTwo I ↔ centralizer (pCore 2 I : Set I) ≤ pCore 2 I :=
  ⟨centralizer_twoCore_le, hasCharacteristicTwo_of_centralizer⟩

/-- Every intermediate overgroup of the fixed Sylow subgroup inherits
characteristic two. The conclusion concerns the literal subgroup `K`. -/
theorem characteristicTwo_of_sylow_overgroup {S I K : Subgroup G}
    (hS : Chapter1.IsSylowIn 2 S I) (hKI : K ≤ I) (hSK : S ≤ K)
    (hI : HasCharacteristicTwo I) : HasCharacteristicTwo K := by
  apply hasCharacteristicTwo_of_centralizer
  apply Stellmacher.characteristicTwo_of_contains_core_in I K (centralizer_twoCore_le hI) hKI
  obtain ⟨P, hP⟩ := hS
  exact (map_mono (pCore_isPGroup.le_sylow_of_normal P)).trans (hP ▸ hSK)

omit [Finite G] in
/-- The ambient two-core is contained in the two-core of an intermediate
Sylow overgroup. -/
theorem twoCoreIn_le_of_sylow_overgroup {S I K : Subgroup G}
    (hS : Chapter1.IsSylowIn 2 S I) (hKI : K ≤ I) (hSK : S ≤ K) :
    I.pCoreIn 2 ≤ K.pCoreIn 2 := by
  obtain ⟨P, hP⟩ := hS
  have hQK : I.pCoreIn 2 ≤ K := (pCoreIn_le_sylow I P).trans (hP ▸ hSK)
  apply le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 I) hQK
  exact hKI.trans (by
    simpa only [pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using (pCore 2 I).le_normalizer_map I.subtype)

namespace LocalData
variable (d : LocalData G)

omit [Finite G] in
/-- The source outside family really supplies containment of `Y₊S`. -/
theorem join_le_of_mem_Hplus {I : Subgroup G} (hI : I ∈ d.Hplus) :
    d.Yplus ⊔ d.S ≤ I := hI.1.2

omit [Finite G] in
/-- A Sylow overgroup below an outside member is again in the genuine
outside family whenever it is not contained in `M`. -/
theorem mem_Hplus_of_intermediate {I K : Subgroup G}
    (hI : I ∈ d.Hplus) (hS : Chapter1.IsSylowIn 2 d.S I)
    (hKI : K ≤ I) (hYK : d.Yplus ⊔ d.S ≤ K) (hKM : ¬ K ≤ d.M) :
    K ∈ d.Hplus := by
  refine ⟨⟨?_, hYK⟩, hKM⟩
  intro hbot
  exact hI.1.1 (le_bot_iff.mp ((twoCoreIn_le_of_sylow_overgroup hS hKI
    (le_sup_right.trans hYK)).trans_eq hbot))

/-- Characteristic two descends along outside overgroups. -/
theorem characteristicTwo_of_mem_Hplus_le {I K : Subgroup G}
    (hS : Chapter1.IsSylowIn 2 d.S I) (hKI : K ≤ I)
    (hK : K ∈ d.Hplus) (hf : HasCharacteristicTwo I) :
    HasCharacteristicTwo K :=
  characteristicTwo_of_sylow_overgroup hS hKI
    (le_sup_right.trans (d.join_le_of_mem_Hplus hK)) hf

/-- A contrary outside subgroup contains a minimal outside subgroup which
still has characteristic two. This minimizes in the genuine `H₊` family. -/
theorem exists_minimal_outside_characteristicTwo {I : Subgroup G}
    (hI : I ∈ d.Hplus) (hS : Chapter1.IsSylowIn 2 d.S I)
    (hf : HasCharacteristicTwo I) :
    ∃ K : Subgroup G, K ≤ I ∧ K ∈ d.HplusMinimal ∧ HasCharacteristicTwo K := by
  obtain ⟨K, hKI, hK⟩ := exists_minimal_le_of_wellFoundedLT
    (fun K : Subgroup G => K ∈ d.Hplus) I hI
  exact ⟨K, hKI, hK, d.characteristicTwo_of_mem_Hplus_le hS hKI hK.1 hf⟩

end LocalData

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo
end
