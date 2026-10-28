module

public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Sylow

/-!
# A regular elementary eight group inside the canonical Sylow

The three translations of the binary cube are the product of all four pair
swaps, the product of the two swaps of pairs, and the interchange of the
four-point blocks. Their eight words act regularly and are even permutations.
The standard `D`, the exceptional group, and this regular group generate the
canonical Sylow: the exceptional group supplies the first swap of pairs, and
the regular group then supplies the second one and the block interchange.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Proposition B.3.2(3),(6), printed pp. 83–84. This is the subgroup-containment
input for the generated-offender calculation.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterB.Offenders.Eight

open Representation.BinaryOffender

def standardRegularWords (i : Fin 8) : Perm :=
  cubeWords (dWords 15) (kleinSecond 8 (by decide) * secondBlockSwap) halfSwap 1
    ⟨i.val, by omega⟩

def standardRegular : Subgroup Perm where
  carrier := Set.range standardRegularWords
  one_mem' := ⟨0, rfl⟩
  mul_mem' := by
    have h : ∀ i j, ∃ k, standardRegularWords i * standardRegularWords j = standardRegularWords k := by decide +kernel
    rintro a b ⟨i, rfl⟩ ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := h i j
    exact ⟨k, hk.symm⟩
  inv_mem' := by
    have h : ∀ i, (standardRegularWords i)⁻¹ = standardRegularWords i := by decide +kernel
    rintro a ⟨i, rfl⟩
    exact ⟨i, (h i).symm⟩

theorem standardRegularWords_mem (i : Fin 8) : standardRegularWords i ∈ standardRegular := ⟨i, rfl⟩

theorem card_standardRegular : Nat.card standardRegular = 8 := by
  change Nat.card (Set.range standardRegularWords) = 8
  rw [← Nat.card_congr (Equiv.ofInjective standardRegularWords (by decide +kernel))]
  simp

theorem isRegularEight_standardRegular : IsRegularEight standardRegular := by
  have he : IsElementaryTwo standardRegular := by
    refine ⟨?_, ?_⟩
    · intro h
      have hc := card_standardRegular
      rw [h, Subgroup.card_bot] at hc
      contradiction
    · have hc : ∀ i j, standardRegularWords i * standardRegularWords j = standardRegularWords j * standardRegularWords i := by
        decide +kernel
      have hs : ∀ i, standardRegularWords i ^ 2 = 1 := by decide +kernel
      refine { toIsMulCommutative := ⟨⟨?_⟩⟩, exponent_dvd_p := ?_ }
      · rintro ⟨a, i, rfl⟩ ⟨b, j, rfl⟩
        exact Subtype.ext (hc i j)
      · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
        rintro ⟨a, i, rfl⟩
        exact Subtype.ext (hs i)
  refine ⟨he, card_standardRegular, ?_, ?_⟩
  · have hs : ∀ i, Equiv.Perm.sign (standardRegularWords i) = 1 := by decide +kernel
    rintro g ⟨i, rfl⟩
    exact hs i
  · have ht : ∀ x y : Fin 8, ∃! i : Fin 8, standardRegularWords i x = y := by
      unfold ExistsUnique
      decide +kernel
    intro x y
    obtain ⟨i, hi, hu⟩ := ht x y
    refine ⟨⟨standardRegularWords i, standardRegularWords_mem i⟩, hi, ?_⟩
    rintro ⟨a, j, rfl⟩ hj
    exact Subtype.ext (congrArg standardRegularWords (hu j hj))

theorem standardRegular_le_canonicalSylow : standardRegular ≤ canonicalSylow := by
  rintro g ⟨i, rfl⟩
  have hd : dWords 15 ∈ canonicalSylow :=
    D_le_canonicalSylow ((mem_disjointTranspositions_iff 4 _).mpr ⟨15, rfl⟩)
  have hb : kleinSecond 8 (by decide) * secondBlockSwap ∈ canonicalSylow :=
    canonicalSylow.mul_mem (sylowGenerators_mem 4) (sylowGenerators_mem 5)
  have hh : halfSwap ∈ canonicalSylow := sylowGenerators_mem 6
  unfold standardRegularWords cubeWords
  repeat' apply Subgroup.mul_mem
  all_goals split_ifs
  all_goals first | exact hd | exact hb | exact hh | exact Subgroup.one_mem _

theorem canonicalSylow_le_of_D_exceptional_regular (P : Subgroup Perm)
    (hD : D 8 ≤ P) (hE : exceptional 8 (by decide) ≤ P) (hR : standardRegular ≤ P) :
    (canonicalSylow : Subgroup Perm) ≤ P := by
  have hb : kleinSecond 8 (by decide) ∈ P :=
    hE (Subgroup.subset_closure (Or.inl (Or.inr (Set.mem_singleton _))))
  have hbc : kleinSecond 8 (by decide) * secondBlockSwap ∈ P := by
    have := hR (standardRegularWords_mem 2)
    simpa [standardRegularWords, cubeWords] using this
  have hc : secondBlockSwap ∈ P := by
    simpa only [inv_mul_cancel_left] using P.mul_mem (P.inv_mem hb) hbc
  have hh : halfSwap ∈ P := by
    have := hR (standardRegularWords_mem 4)
    simpa [standardRegularWords, cubeWords] using this
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact hD (pairSwap_mem 0 (by decide))
  · exact hD (pairSwap_mem 1 (by decide))
  · exact hD (pairSwap_mem 2 (by decide))
  · exact hD (pairSwap_mem 3 (by decide))
  · exact hb
  · exact hc
  · exact hh

theorem D_sup_exceptional_sup_regular :
    D 8 ⊔ exceptional 8 (by decide) ⊔ standardRegular = (canonicalSylow : Subgroup Perm) := by
  apply le_antisymm
  · exact sup_le (sup_le D_le_canonicalSylow exceptional_le_canonicalSylow)
      standardRegular_le_canonicalSylow
  · exact canonicalSylow_le_of_D_exceptional_regular _
      (le_sup_of_le_left le_sup_left) (le_sup_of_le_left le_sup_right) le_sup_right

end CFSG.Quasithin.ChapterB.Offenders.Eight
