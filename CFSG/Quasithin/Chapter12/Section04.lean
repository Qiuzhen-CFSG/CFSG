module

public import Theory.GroupTheory.WeaklyClosedCommutator

/-!
# Further reductions: the fusion obstruction

Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, §12.4, printed pp. 812–816 (PDF pp. 829–833).
The section continues onto p. 816, including the end of Lemma 12.4.8,
Lemma 12.4.9 and the final proof of Theorem 12.4.2.

This module proves the final fusion argument of Lemma 12.4.9. Put
`A = V^g` and `D = [V,A]`. The module calculations give `D^g = D` and
`z ∈ D`, where `z` is fixed by `L`. Control of fusion by `L` then makes `z`
weakly closed in `V`. Hence `g` centralizes `z`, so it normalizes `V`,
contradicting a nontrivial commutator.

The full source theorem still requires the conjugate-existence lemma 12.4.1,
the `L₅(2)` exclusion 12.4.4, the small-module fusion and symmetry results,
and the weak-closure bound 12.4.8. The result below is only their fusion
interface, not an assertion of Theorem 12.4.2 with those results assumed.
-/

namespace CFSG.Quasithin.Chapter12.Section04

open Subgroup

/-- The final step of Lemma 12.4.9, for either small-module case.
The symmetry hypothesis is the actual commutator equality proved by the
module calculations; fusion is stated only for the distinguished element. -/
public theorem commutator_eq_bot_of_fusion_and_symmetry
    {G : Type*} [Group G] {V L : Subgroup G} [IsMulCommutative V]
    {z g : G}
    (hL : L ≤ centralizer {z})
    (hfusion : ∀ a : G, MulAut.conj a z ∈ V →
      ∃ l ∈ L, MulAut.conj a z = MulAut.conj l z)
    (hcentral : centralizer {z} ≤ normalizer (V : Set G))
    (hnorm : V.map (MulAut.conj g).toMonoidHom ≤ normalizer (V : Set G))
    (hz : z ∈ ⁅V, V.map (MulAut.conj g).toMonoidHom⁆)
    (hsymmetry : (⁅V, V.map (MulAut.conj g).toMonoidHom⁆).map
        (MulAut.conj g).toMonoidHom = ⁅V, V.map (MulAut.conj g).toMonoidHom⁆) :
    ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  apply commutator_conjugate_eq_bot_of_weakly_closed_element
    (z := z) ?_ hcentral hz (le_normalizer_iff_commutator_le_left.mp hnorm) hsymmetry
  intro a ha
  exact mul_inv_eq_iff_eq_mul.mpr
    (mem_centralizer_singleton_iff.mp (centralizes_of_element_fusion hL hfusion ha))

end CFSG.Quasithin.Chapter12.Section04
