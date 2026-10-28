module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Reduction
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Representatives
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.CoreWitness
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.TwoGroup

/-!
# Ambient Held interval normalizers lie in the literal local overgroup

Sylow conjugacy inside each literal local reduces an arbitrary ambient Sylow
contained there to the fixed conjugate of the published four-word subgroup.
The embedded local two-core is preserved under this conjugation, and relative
index is preserved by the conjugation equivalence. Schreier's lemma then
covers the proper index-two cases by the explicit entries in Representatives.

The published representative is a self-normalizing two-group, as proved by
the checked orbit and colored-graph certificates. The max3 and max4 finite
calculations bound every selected entry's normalizer in the corresponding
literal local. The theorem `normalizer_le` discharges all certificate inputs
and proves the ambient containment for the actual embedded local two-core.
No simplicity, automorphism-realization, or outer-quotient premise is needed.
The conditional reductions remain available. No pair-placement theorem,
residual, or local quotient calculation is used.

Sources: GLS3 Table 5.3p; ATLAS max3/max4 programs. This is an additional Held
calculation, not the Lie-type argument on quasithin pp.747–748.
-/

public section

open Subgroup
open scoped Pointwise
namespace Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient
open Held.LocalPairs.SylowGeometry.Calculations

/-- Conjugacy inside the literal local transports a fixed-Sylow calculation. -/
theorem normalizer_le_of_fixed_sylow
    (i : Bool) (T : Sylow 2 Held.He)
    (hT : (T : Subgroup Held.He) ≤ localOvergroup i)
    (hfixed : ∀ V : Subgroup Held.He, localTwoCore i ≤ V → V ≤ T →
      V.relIndex T ≤ 2 → normalizer (V : Set Held.He) ≤ localOvergroup i)
    (S : Sylow 2 Held.He) (hS : (S : Subgroup Held.He) ≤ localOvergroup i)
    (U : Subgroup Held.He) (hC : localTwoCore i ≤ U) (hUS : U ≤ S)
    (hidx : U.relIndex S ≤ 2) :
    normalizer (U : Set Held.He) ≤ localOvergroup i := by
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq (localOvergroup i)
    (S.subtype hS) (T.subtype hT)
  have hST : (S : Subgroup Held.He).map (MulAut.conj (m : Held.He)).toMonoidHom = T :=
    congrArg Sylow.toSubgroup (Sylow.subtype_injective ((S.smul_subtype hS m).symm.trans hm))
  have hM : (localOvergroup i).map (MulAut.conj (m : Held.He)).toMonoidHom = localOvergroup i :=
    mem_normalizer_iff_map_conj_eq.mp ((localOvergroup i).le_normalizer m.property)
  have hcore : (localTwoCore i).map (MulAut.conj (m : Held.He)).toMonoidHom = localTwoCore i :=
    mem_normalizer_iff_map_conj_eq.mp (localOvergroup_le_normalizer_localTwoCore i m.property)
  have hN := hfixed (U.map (MulAut.conj (m : Held.He)).toMonoidHom)
    (hcore ▸ map_mono hC) (hST ▸ map_mono hUS) (by
      rw [← hST, relIndex_map_map_of_injective _ _ (MulAut.conj (m : Held.He)).injective]
      exact hidx)
  apply (map_le_map_iff_of_injective (f := (MulAut.conj (m : Held.He)).toMonoidHom)
    (MulAut.conj (m : Held.He)).injective).mp
  rwa [map_equiv_normalizer_eq, hM]

/-- The remaining mathematical inputs are the existing representative
self-normalizer calculation and bounds on explicit proper index-two entries.
The whole-Sylow case and all conjugacy/exhaustiveness steps are discharged. -/
theorem normalizer_le_of_entry_bounds
    (i : Bool)
    (hn : normalizer (representative : Set He) = representative)
    (hentries : ∀ (k : Fin 4) (mask : Fin 4 → Bool), mask k = true →
      localTwoCore i ≤ entry i k mask →
      (entry i k mask).relIndex (fixedSubgroup i) = 2 →
      normalizer (entry i k mask : Set He) ≤ localOvergroup i)
    (S : Sylow 2 He) (hS : (S : Subgroup He) ≤ localOvergroup i)
    (U : Subgroup He) (hC : localTwoCore i ≤ U) (hUS : U ≤ S)
    (hidx : U.relIndex S ≤ 2) :
    normalizer (U : Set He) ≤ localOvergroup i := by
  obtain ⟨P, hP⟩ := exists_representative_sylow representative_isPGroup hn
  let T : Sylow 2 He := fixedConjugator i • P
  have hT : (T : Subgroup He) = fixedSubgroup i := by
    change (P : Subgroup He).map (MulAut.conj (fixedConjugator i)).toMonoidHom = _
    rw [hP]
    rfl
  have hTM : (T : Subgroup He) ≤ localOvergroup i :=
    hT ▸ fixedSubgroup_le_localOvergroup i
  apply normalizer_le_of_fixed_sylow i T hTM ?_ S hS U hC hUS hidx
  intro V hCV hVT hvi
  by_cases he : V = (T : Subgroup He)
  · rw [he]
    change normalizer (T : Set He) ≤ localOvergroup i
    rw [inner_self_normalizing_of_representative representative_isPGroup hn T]
    exact hTM
  · have hi1 : V.relIndex (T : Subgroup He) ≠ 1 := by
      intro hi
      exact he (le_antisymm hVT (relIndex_eq_one.mp hi))
    have hi0 : V.relIndex (T : Subgroup He) ≠ 0 :=
      ne_zero_of_dvd_ne_zero (Finite.card_pos (α := T)).ne' (V.relIndex_dvd_card T)
    have hi2 : V.relIndex (fixedSubgroup i) = 2 := by rw [← hT]; omega
    obtain ⟨k, mask, hk, hv⟩ := exists_entry_of_relIndex_two i V (hT ▸ hVT) hi2
    rw [← hv] at hCV hi2 ⊢
    exact hentries k mask hk hCV hi2

/-- A single certified core word suffices to select the finite entries.
This allows the finite calculations to avoid any assumed identification
or order of the local two-core. -/
theorem normalizer_le_of_entry_word_bounds
    (i : Bool)
    (hn : normalizer (representative : Set He) = representative)
    (hentries : ∀ (k : Fin 4) (mask : Fin 4 → Bool), mask k = true →
      localWord i ^ (if i then 5 else 6) ∈ entry i k mask →
      (entry i k mask).relIndex (fixedSubgroup i) = 2 →
      normalizer (entry i k mask : Set He) ≤ localOvergroup i)
    (S : Sylow 2 He) (hS : (S : Subgroup He) ≤ localOvergroup i)
    (U : Subgroup He) (hC : localTwoCore i ≤ U) (hUS : U ≤ S)
    (hidx : U.relIndex S ≤ 2) :
    normalizer (U : Set He) ≤ localOvergroup i := by
  apply normalizer_le_of_entry_bounds i hn ?_ S hS U hC hUS hidx
  intro k mask hk hcore hi
  exact hentries k mask hk (hcore (localWord_power_mem_localTwoCore i)) hi

/-- In either literal Held local overgroup M, every subgroup U between its
embedded two-core and an ambient Sylow two-subgroup S contained in M, with
[S : U] at most two, has its full inner normalizer contained in M.
All representative and finite-entry certificate premises are discharged. -/
theorem normalizer_le
    (i : Bool) (S : Sylow 2 He) (hS : (S : Subgroup He) ≤ localOvergroup i)
    (U : Subgroup He) (hC : localTwoCore i ≤ U) (hUS : U ≤ S)
    (hidx : U.relIndex S ≤ 2) :
    normalizer (U : Set He) ≤ localOvergroup i := by
  apply normalizer_le_of_entry_word_bounds i InnerNormalizer.normalizer_eq ?_
    S hS U hC hUS hidx
  cases i
  · exact Max3.entry_normalizer_le InnerNormalizer.orbitSizeLabel_eq_card_orbit
  · exact Max4.entry_normalizer_le InnerNormalizer.orbitSizeLabel_eq_card_orbit

end Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient
