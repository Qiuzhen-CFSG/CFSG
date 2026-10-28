module

public import CFSG.Quasithin.ChapterE.Section03.Offenders.Basic
public import Theory.GroupTheory.AbelianConjugateSpan

/-!
# Zeroth weak closure and local orbit spans

If the global parameter `s` exceeds the fixed-space parameter `a`, a conjugate
of V contained in a normalizing subgroup cannot act nontrivially on V:
E.3.10 would give `s ≤ a`. Thus the actual zeroth weak closure centralizes V.
For a relatively normal subgroup Q of H, its weak closure is H-invariant,
so this centralization extends to the whole H-conjugate span of V.

Source: Aschbacher--Smith, E.3.21(1), and its application in 15.2.26(2--3),
printed pp.235 and 1118.
-/

public section

open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.ChapterE

variable {G : Type*} [Group G] [Finite G]

/-- Hyperplane centralizer control is enough to make the literal global
minimum exceed one; the corank-zero case is the whole module. -/
theorem one_lt_globalR_of_hyperplane_centralizers
    (V : Subgroup G) [IsElementaryAbelian 2 V]
    (hhyper : ∀ U ≤ V, subgroupCorank V U = 1 →
      centralizer (U : Set G) ≤ normalizer (V : Set G)) :
    1 < globalR V := by
  have hbound : (2 : ℕ∞) ≤ globalR V := by
    apply le_iInf
    intro U
    apply le_iInf
    rintro ⟨hUV, hescape⟩
    have hn : 2 ≤ subgroupCorank V U := by
      by_contra hsmall
      have hcases : subgroupCorank V U = 0 ∨ subgroupCorank V U = 1 := by omega
      rcases hcases with hzero | hone
      · have he := subgroup_eq_of_corank_zero hUV hzero
        subst U
        exact hescape (Subgroup.centralizer_le_normalizer _)
      · exact hescape (hhyper U hUV hone)
    exact_mod_cast hn
  exact lt_of_lt_of_le (by norm_num) hbound

/-- The zero-index case of E.3.21(1), for the actual conjugate family. -/
theorem weakClosure_zero_le_centralizer_of_localA_lt_globalS
    (V X : Subgroup G) [IsElementaryAbelian 2 V]
    (hXN : X ≤ normalizer (V : Set G)) (ha : localA V < globalS V) :
    indexedWeakClosure V X 0 ≤ X ⊓ centralizer (V : Set G) := by
  refine le_inf (indexedWeakClosure_le V X 0) ?_
  rw [weakClosure_eq_sSup_gamma]
  apply sSup_le
  intro A hA
  obtain ⟨g, rfl, hAX⟩ := (mem_gamma_zero_iff V X A).mp hA
  have hAN := hAX.trans hXN
  apply le_centralizer_iff.mpr
  apply commutator_eq_bot_iff_le_centralizer.mp
  by_contra hmove
  have hc : subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      (V.map (MulAut.conj g).toMonoidHom ⊓ normalizer (V : Set G)) = 0 := by
    rw [inf_eq_left.mpr hAN]
    norm_num [subgroupCorank]
  have hs : (0 : ℕ∞) < globalS V := lt_of_le_of_lt zero_le ha
  have h := (lemma_E_3_10 V g (by simpa only [hc, Nat.cast_zero] using hs) hmove).2.2.1
  rw [hc, Nat.cast_zero] at h
  exact (not_le_of_gt ha) (tsub_eq_zero_iff_le.mp (le_antisymm h zero_le))

/-- Relative normality of Q propagates a weak-closure centralizer bound to
the literal H-conjugate span. No ambient normality is required. -/
theorem weakClosure_le_centralizer_conjugateSpanBy
    (V X H Q : Subgroup G) (i : ℕ)
    (hQX : Q ≤ X) (hQH : Q ≤ H) (hHQ : H ≤ normalizer (Q : Set G))
    (hW : indexedWeakClosure V X i ≤ centralizer (V : Set G)) :
    indexedWeakClosure V Q i ≤ H ⊓ centralizer (conjugateSpanBy V H : Set G) := by
  refine le_inf ((indexedWeakClosure_le V Q i).trans hQH) ?_
  exact le_centralizer_conjugateSpanBy_of_normalizes _ V H
    (hHQ.trans (normalizer_le_weakClosure_normalizer V Q i))
    ((weakClosure_mono V i hQX).trans hW)

end CFSG.Quasithin.ChapterE
