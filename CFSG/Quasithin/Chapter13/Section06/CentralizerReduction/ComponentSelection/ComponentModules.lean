module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.ActionKernels

/-!
# Module transport for the selected centralizer component

The full star preimage differs from its original subgroup by elements
centralizing U_v. Those extra elements change neither the seed span nor
its commutator. This identifies U_X at K* with the literal ambient
commutator after the T_v-orbit of K is known to be trivial.

Together with ActionKernels this proves the quotient and transport steps
needed for 13.6.14–15. The contrary orbit-of-two argument, including its
Baumann/Borel calculation, and the offender/projection argument excluding
the A₅ module remain to be assembled. In particular the final theorem
here assumes invariance explicitly and is not a proof of 13.6.14.

Source: Aschbacher–Smith, The Classification of Quasithin Groups, combined
1 March 2004 manuscript, printed pp.929–930.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
variable {G : Type*} [Group G]

/-- Enlarging a conjugator subgroup by the star kernel does not change its
seed span inside U_v. -/
theorem seedSpan_starPreimage_starImage (H L : Subgroup G) (z v : G)
    (hH : H ≤ Gv v) :
    conjugateSpanBy (zpowers z) (starPreimage z v (starImage z v H) ⊔ Lv L v) =
      conjugateSpanBy (zpowers z) (H ⊔ Lv L v) := by
  let W := conjugateSpanBy (zpowers z) (H ⊔ Lv L v)
  have hWU : W ≤ Uv z v :=
    conjugateSpanBy_mono le_rfl (sup_le hH (Lv_le_Gv L v))
  apply le_antisymm
  · apply conjugateSpanBy_le (le_conjugateSpanBy _ _)
    apply sup_le ?_ (le_sup_right.trans (le_normalizer_conjugateSpanBy _ _))
    intro x hx
    obtain ⟨k, hk, c, hc, rfl⟩ := starPreimage_starImage_factor z v H hx
    exact mul_mem ((le_normalizer_conjugateSpanBy (zpowers z) (H ⊔ Lv L v))
      ((show H ≤ H ⊔ Lv L v from le_sup_left) hk))
      (Subgroup.centralizer_le_normalizer _ (centralizer_le hWU hc.2))
  · exact conjugateSpanBy_mono le_rfl
      (sup_le_sup_right (le_starPreimage_starImage z v H hH) _)

/-- The same kernel also disappears from commutators on any subgroup of U_v. -/
theorem commutator_starPreimage_starImage (W H : Subgroup G) (z v : G)
    (hW : W ≤ Uv z v) (hH : H ≤ Gv v) :
    ⁅W, starPreimage z v (starImage z v H)⁆ = ⁅W, H⁆ := by
  apply le_antisymm
  · apply commutator_le.mpr
    intro w hw x hx
    obtain ⟨k, hk, c, hc, rfl⟩ := starPreimage_starImage_factor z v H hx
    have hcomm : Commute w c := mem_centralizer_iff.mp hc.2 w (hW hw)
    rw [commutatorElement_mul_right_eq_mul_conj, hcomm.commutator_eq]
    simpa using commutator_mem_commutator hw hk
  · exact commutator_mono le_rfl (le_starPreimage_starImage z v H hH)

/-- U_X at the star image of H has the literal ambient commutator formula. -/
theorem UX_starImage (H L : Subgroup G) (z v : G) (hH : H ≤ Gv v) :
    UX L z v (starImage z v H) =
      ⁅conjugateSpanBy (zpowers z) (H ⊔ Lv L v), H⁆ := by
  rw [UX, seedSpan_starPreimage_starImage H L z v hH]
  exact commutator_starPreimage_starImage _ H z v
    (conjugateSpanBy_mono le_rfl (sup_le hH (Lv_le_Gv L v))) hH

theorem Kminus_eq_of_invariant (K T : Subgroup G) (v : G)
    (hn : Tv T v ≤ normalizer (K : Set G)) : Kminus K T v = K :=
  le_antisymm (conjugateSpanBy_le le_rfl hn) (le_conjugateSpanBy K (Tv T v))

/-- Once the orbit-of-two case is excluded, the two remaining clauses of
13.6.14 follow without additional representation hypotheses. This lemma does
not assert the required invariance of K. -/
theorem invariant_component_consequences (K L T : Subgroup G) (z v : G)
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G)) :
    starImage z v K ∈ Xz L T z v ∧
      UX L z v (starImage z v K) = ⁅WK K L T z v, K⁆ := by
  constructor
  · have h := hK.2.2
    rw [← starImage_Kminus K T z v hK.1.1, Kminus_eq_of_invariant K T v hn] at h
    exact h
  · rw [UX_starImage K L z v hK.1.1, WK, Kminus_eq_of_invariant K T v hn]

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
end
