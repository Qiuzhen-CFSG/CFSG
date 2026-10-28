module
public import Mathlib.GroupTheory.Commutator.Basic
/-!
# Centrality in a pair of commuting conjugate factors

If a subgroup of an internal direct product commutes modulo a subgroup fixed
pointwise by an element exchanging the two factors, then it centralizes the
whole product. The fixed subgroup meets either factor trivially; each factor
commutator lies in that intersection.

This is the direct-product step in the final contradiction of
Aschbacher–Smith 14.6.9, applied to the literal two-core of Mc.
-/

public section
open Subgroup
open scoped commutatorElement
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

theorem centralizes_sup_of_commutator_le_fixed_swap
    (V Z R1 R2 : Subgroup G) (t : G)
    (hV : V ≤ R1 ⊔ R2) (hcomm : ⁅V, R1 ⊔ R2⁆ ≤ Z)
    (hd : Disjoint R1 R2) (hc : R1 ≤ centralizer (R2 : Set G))
    (ht : t ∈ centralizer (Z : Set G))
    (hswap : R1.map (MulAut.conj t).toMonoidHom = R2) :
    V ≤ centralizer ((R1 ⊔ R2 : Subgroup G) : Set G) := by
  have hfix (z : G) (hz : z ∈ Z) : (MulAut.conj t) z = z := by
    change t * z * t⁻¹ = z
    rw [← ht z hz, mul_inv_cancel_right]
  have hZR1 : Z ⊓ R1 = ⊥ := by
    apply eq_bot_iff.mpr
    intro z hz
    have hz2 : z ∈ R2 := by
      rw [← hswap, ← hfix z hz.1]
      exact mem_map_of_mem _ hz.2
    exact (show R1 ⊓ R2 ≤ ⊥ from (disjoint_iff.mp hd).le) ⟨hz.2,hz2⟩
  have hZR2 : Z ⊓ R2 = ⊥ := by
    apply eq_bot_iff.mpr
    intro z hz
    have hz1 : z ∈ R1 := by
      obtain ⟨x,hx,he⟩ := (show z ∈ R1.map (MulAut.conj t).toMonoidHom from hswap ▸ hz.2)
      have heq : x = z := (MulAut.conj t).injective (he.trans (hfix z hz.1).symm)
      exact heq ▸ hx
    exact (show R1 ⊓ R2 ≤ ⊥ from (disjoint_iff.mp hd).le) ⟨hz1,hz.2⟩
  have hN1 : R1 ⊔ R2 ≤ normalizer (R1 : Set G) :=
    sup_le R1.le_normalizer ((le_centralizer_iff.mp hc).trans (centralizer_le_normalizer _))
  have hN2 : R1 ⊔ R2 ≤ normalizer (R2 : Set G) :=
    sup_le (hc.trans (centralizer_le_normalizer _)) R2.le_normalizer
  have hc1 : V ≤ centralizer (R1 : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply bot_unique
    rw [← hZR1]
    exact le_inf ((commutator_mono le_rfl le_sup_left).trans hcomm)
      (le_normalizer_iff_commutator_le_right.mp (hV.trans hN1))
  have hc2 : V ≤ centralizer (R2 : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply bot_unique
    rw [← hZR2]
    exact le_inf ((commutator_mono le_rfl le_sup_right).trans hcomm)
      (le_normalizer_iff_commutator_le_right.mp (hV.trans hN2))
  exact le_centralizer_iff.mpr (sup_le (le_centralizer_iff.mp hc1) (le_centralizer_iff.mp hc2))
end Theory.GroupTheory
