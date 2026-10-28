module

public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Weakly closed elements and conjugate commutators

An element whose fusion in `V` is controlled by a subgroup centralizing it is
weakly closed in `V`. If its centralizer lies in `N`, the normalizer of every
subgroup of `V` containing the element also lies in `N`. For abelian `V`, this
forces a conjugate commutator fixed by its conjugating element to be trivial,
provided the element centralizer normalizes `V`.

This is the final group-theoretic argument in Aschbacher–Smith,
*The Classification of Quasithin Groups*, combined 1 March 2004 manuscript,
Lemma 12.4.9, printed p. 816. The module calculations establishing the symmetry
of the commutator and the fusion hypotheses are separate inputs.
-/

namespace Subgroup
variable {G : Type*} [Group G]

/-- Fusion controlled by a subgroup centralizing `z` forces every transporter
of `z` into `V` to centralize `z`. -/
public theorem centralizes_of_element_fusion
    {V L : Subgroup G} {z g : G}
    (hL : L ≤ centralizer {z})
    (hfusion : ∀ a : G, MulAut.conj a z ∈ V →
      ∃ l ∈ L, MulAut.conj a z = MulAut.conj l z)
    (hg : MulAut.conj g z ∈ V) : g ∈ centralizer {z} := by
  obtain ⟨l, hl, heq⟩ := hfusion g hg
  have hlz := mem_centralizer_singleton_iff.mp (hL hl)
  have hfix : MulAut.conj g z = z := by
    rw [heq, MulAut.conj_apply, hlz]
    simp only [mul_assoc, mul_inv_cancel, mul_one]
  apply mem_centralizer_singleton_iff.mpr
  exact (mul_inv_eq_iff_eq_mul.mp hfix)

/-- The centralizer of a weakly closed element controls the normalizers of
all intermediate subgroups containing it. -/
public theorem normalizer_le_of_weakly_closed_element
    {V D N : Subgroup G} {z : G}
    (hz : z ∈ D) (hDV : D ≤ V)
    (hweak : ∀ a : G, MulAut.conj a z ∈ V → MulAut.conj a z = z)
    (hcentral : centralizer {z} ≤ N) : normalizer (D : Set G) ≤ N := by
  intro a ha
  apply hcentral
  apply mem_centralizer_singleton_iff.mpr
  apply mul_inv_eq_iff_eq_mul.mp
  apply hweak
  apply hDV
  have heq := mem_normalizer_iff_map_conj_eq.mp ha
  rw [← heq]
  exact mem_map_of_mem (MulAut.conj a).toMonoidHom hz

/-- An invariant conjugate commutator containing a weakly closed element
vanishes if the element centralizer normalizes the abelian subgroup. -/
public theorem commutator_conjugate_eq_bot_of_weakly_closed_element
    {V : Subgroup G} [IsMulCommutative V] {z g : G}
    (hweak : ∀ a : G, MulAut.conj a z ∈ V → MulAut.conj a z = z)
    (hcentral : centralizer {z} ≤ normalizer (V : Set G))
    (hz : z ∈ ⁅V, V.map (MulAut.conj g).toMonoidHom⁆)
    (hcomm : ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≤ V)
    (hfixed : (⁅V, V.map (MulAut.conj g).toMonoidHom⁆).map (MulAut.conj g).toMonoidHom =
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆) :
    ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  have hg : g ∈ normalizer (V : Set G) :=
    normalizer_le_of_weakly_closed_element hz hcomm hweak hcentral
      (mem_normalizer_iff_map_conj_eq.mpr hfixed)
  have heq : V.map (MulAut.conj g).toMonoidHom = V :=
    mem_normalizer_iff_map_conj_eq.mp hg
  rw [heq]
  exact commutator_self_eq_bot_iff.mpr inferInstance

end Subgroup
