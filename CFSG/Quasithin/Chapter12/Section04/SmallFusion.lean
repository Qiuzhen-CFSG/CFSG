module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.Setup
public import Theory.GroupTheory.WeaklyClosedCommutator

/-!
# Fusion and symmetry obstruction for the small-module cases

This leaf exports the exact final argument of Lemma 12.4.9 without importing
the Section 12.4 assembly. Put `A = V^g` using the repository's left
conjugation convention. The B.4 module calculation supplies the symmetry of
`[V,A]` and its distinguished element; weak closure from Lemma 12.4.7 then
forces the commutator to vanish, contradicting its nontriviality.

The setup and the module calculations remain separate source inputs. In
particular this theorem does not replace the original V by its natural
quotient and does not assume the desired classification conclusion.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, Lemma 12.4.9,
printed p.816 (PDF p.833).
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion

/-- The symmetry obstruction in the exact ambient subgroup notation. The
hypotheses `hfixed` and `hz` are the two B.4 module calculations: symmetry of
the commutator under conjugation by `g`, and inclusion of the generator `z`.
Fusion is stated for the distinguished element, as in Lemma 12.4.7. -/
theorem lemma_12_4_9
    {G : Type*} [Group G] {V : Subgroup G} [IsMulCommutative V]
    {L : Subgroup G} {z g : G}
    (hL : L ≤ centralizer {z})
    (hA_normal : V.map (MulAut.conj g).toMonoidHom ≤
      normalizer (V : Set G))
    (hfusion : ∀ a : G, MulAut.conj a z ∈ V →
      ∃ l ∈ L, MulAut.conj a z = MulAut.conj l z)
    (hcentral : centralizer {z} ≤ normalizer (V : Set G))
    (hz : z ∈ ⁅V, V.map (MulAut.conj g).toMonoidHom⁆)
    (hsymmetry : (⁅V, V.map (MulAut.conj g).toMonoidHom⁆).map
        (MulAut.conj g).toMonoidHom = ⁅V, V.map (MulAut.conj g).toMonoidHom⁆)
    (hnontrivial : ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
    ¬ V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
  intro hV_normal
  have hweak : ∀ a : G, MulAut.conj a z ∈ V → MulAut.conj a z = z := by
    intro a ha
    exact mul_inv_eq_iff_eq_mul.mpr
      (mem_centralizer_singleton_iff.mp (centralizes_of_element_fusion hL hfusion ha))
  have hcomm : ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≤ V :=
    (le_normalizer_iff_commutator_le_left.mp hA_normal)
  have hbot := commutator_conjugate_eq_bot_of_weakly_closed_element
    hweak hcentral hz hcomm hsymmetry
  exact hnontrivial hbot

end CFSG.Quasithin.Chapter12.Section04.SmallFusion
