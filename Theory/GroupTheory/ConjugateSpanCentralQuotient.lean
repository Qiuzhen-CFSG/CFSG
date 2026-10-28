module
public import Theory.GroupTheory.ConjugateSpanSylow
public import Theory.GroupTheory.Commutator.RelativeGeneration

/-!
# Movement of a conjugate span modulo a kernel

Suppose A moves V, Q normalizes V, and J normalizes AQ. Then AQ moves
the full J-span U of V. If [U,Q] lies in a J-invariant subgroup Z of U,
we obtain U = [U,A]Z. The proof uses normality only under the displayed
actors; no subgroup is assumed normal in the entire ambient group.

This supplies the central-Cartan movement step in Aschbacher–Smith
5.1.17, printed p.641 (refs/quasithin.pdf).
-/

public section
namespace Subgroup
variable {G : Type*} [Group G]

/-- Movement passes from a seed to its orbit span when the added normalizing
factor acts trivially modulo the specified invariant subgroup. -/
theorem commutator_span_sup_of_normal_modulo
    (V J A Q Z : Subgroup G)
    (hAJ : A ≤ J) (hQJ : Q ≤ J)
    (hJN : J ≤ normalizer ((A ⊔ Q : Subgroup G) : Set G))
    (hQV : Q ≤ normalizer (V : Set G))
    (hVA : ⁅V,A⁆ = V)
    (hZU : Z ≤ conjugateSpanBy V J)
    (hUQ : ⁅conjugateSpanBy V J,Q⁆ ≤ Z)
    (hJZ : J ≤ normalizer (Z : Set G)) :
    ⁅conjugateSpanBy V J,A⁆ ⊔ Z = conjugateSpanBy V J := by
  let U := conjugateSpanBy V J
  let C := ⁅U,A⁆ ⊔ Z
  have hAU : A ≤ normalizer (U : Set G) :=
    hAJ.trans (le_normalizer_conjugateSpanBy V J)
  have hCU : C ≤ U := sup_le (le_normalizer_iff_commutator_le_left.mp hAU) hZU
  have hAC : A ≤ normalizer (C : Set G) :=
    (le_inf (normalizer_commutator_ge_right U A) (hAJ.trans hJZ)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hQC : Q ≤ normalizer (C : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr
      (((commutator_mono hCU le_rfl).trans hUQ).trans le_sup_right)
  have hVN : ⁅V,A ⊔ Q⁆ = V := by
    apply le_antisymm
    · apply le_normalizer_iff_commutator_le_left.mp
      exact sup_le (le_normalizer_iff_commutator_le_left.mpr hVA.le) hQV
    · exact hVA.symm.le.trans (commutator_mono le_rfl le_sup_left)
  have hUN : ⁅U,A ⊔ Q⁆ = U :=
    commutator_conjugateSpanBy_eq_self V J (A ⊔ Q) (sup_le hAJ hQJ) hJN hVN
  apply le_antisymm hCU
  rw [← hUN,commutator_comm]
  exact commutator_sup_le_of_relative_normal (A ⊔ Q) A Q U C
    (sup_le hAC hQC) le_sup_left le_sup_right
    (by rw [commutator_comm]; exact le_sup_left)
    (by rw [commutator_comm]; exact hUQ.trans le_sup_right)

end Subgroup
