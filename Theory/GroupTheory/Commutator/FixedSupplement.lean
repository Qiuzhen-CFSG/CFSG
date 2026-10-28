module
public import Theory.GroupTheory.Commutator.RelativeGeneration
public import Theory.GroupTheory.ConjugateSpanSylow

/-!
# Extending a commutator bound from a fixed supplement

Suppose H normalizes W and Z, and Z = W B where B centralizes A ≤ H.
Then [Z,〈A^H〉] = [W,〈A^H〉]. The latter commutator is H-invariant;
conjugate the bound [Z,A] ≤ [W,〈A^H〉] and pass to the generated subgroup.
All normalization is relative to H.

Source application: the central hyperplane step of Aschbacher--Smith
14.3.25, printed p.1001. Here Z = Z(U), W = VH, and A = Z(U)^g.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

theorem fixed_supplement_commutator_span
    (H Z W A B : Subgroup G)
    (hAH : A ≤ H) (hZH : Z ≤ H)
    (hHZ : H ≤ normalizer (Z : Set G))
    (hHW : H ≤ normalizer (W : Set G))
    (hsplit : Z = W ⊔ B) (hBA : B ≤ centralizer (A : Set G)) :
    ⁅Z,conjugateSpanBy A H⁆ = ⁅W,conjugateSpanBy A H⁆ := by
  let K := conjugateSpanBy A H
  let D := ⁅W,K⁆
  have hWH : W ≤ H := (le_sup_left.trans_eq hsplit.symm).trans hZH
  have hHD : H ≤ normalizer (D : Set G) := by
    intro h hh
    change h ∈ normalizer ((⁅W,K⁆ : Subgroup G) : Set G)
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hHW hh),
      mem_normalizer_iff_map_conj_eq.mp (le_normalizer_conjugateSpanBy A H hh)]
  have hseed : ⁅Z,A⁆ ≤ D := by
    rw [hsplit]
    apply commutator_sup_le_of_relative_normal H W B A D hHD hWH
      ((le_sup_right.trans_eq hsplit.symm).trans hZH)
    · exact commutator_mono le_rfl (le_conjugateSpanBy A H)
    · exact (commutator_eq_bot_iff_le_centralizer.mpr hBA).le.trans bot_le
  apply le_antisymm
  · rw [commutator_comm]
    conv_lhs => rw [conjugateSpanBy_eq_iSup_conj]
    apply commutator_iSup_le_of_relative_normal H Z D _ hHD
    · intro h
      exact (map_mono hAH).trans_eq (mem_normalizer_iff_map_conj_eq.mp (H.le_normalizer h.property))
    · intro h
      have hh := map_mono (f := (MulAut.conj (h:G)).toMonoidHom) hseed
      have heZ : Z.map (MulAut.conj (h:G)).toMonoidHom = Z :=
        mem_normalizer_iff_map_conj_eq.mp (hHZ h.property)
      have heD : D.map (MulAut.conj (h:G)).toMonoidHom = D :=
        mem_normalizer_iff_map_conj_eq.mp (hHD h.property)
      rw [map_commutator,heZ,heD,commutator_comm] at hh
      exact hh
  · exact commutator_mono (le_sup_left.trans_eq hsplit.symm) le_rfl
end Subgroup
