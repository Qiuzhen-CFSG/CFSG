module
public import Theory.GroupTheory.WeaklyClosedCommutator
public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Tactic.Linarith

/-!
# Balanced centralizers of conjugate abelian subgroups

Equal action indices for equal-order abelian subgroups identify both mutual
centralizers with their intersection once one commutator is the full fixed
subgroup. A weakly closed mark whose centralizer is the original normalizer
then excludes a distinct mutually normalizing conjugate.

This is the finite-group endgame of Aschbacher--Smith 12.4.9, printed p.816.
The equal-index and commutator identities come from the module calculation;
the argument does not require an additional conjugation-invariance premise.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Balanced indices identify both mutual centralizers with the intersection. -/
theorem mutual_centralizers_eq_inf_of_balanced_indices
    (V A : Subgroup G) [IsMulCommutative V] [IsMulCommutative A]
    (hcard : Nat.card V = Nat.card A)
    (hindex : (centralizer (A : Set G)).relIndex V =
      (centralizer (V : Set G)).relIndex A)
    (hcomm : ⁅V,A⁆ = V ⊓ centralizer (A : Set G))
    (hVA : V ≤ normalizer (A : Set G)) :
    V ⊓ centralizer (A : Set G) = V ⊓ A ∧
      A ⊓ centralizer (V : Set G) = V ⊓ A := by
  have hfirst : V ⊓ centralizer (A : Set G) = V ⊓ A := by
    apply le_antisymm
    · exact le_inf inf_le_left (hcomm ▸ le_normalizer_iff_commutator_le_right.mp hVA)
    · exact le_inf inf_le_left (inf_le_right.trans A.le_centralizer)
  refine ⟨hfirst, ?_⟩
  have hle : V ⊓ A ≤ A ⊓ centralizer (V : Set G) :=
    le_inf inf_le_right (inf_le_left.trans V.le_centralizer)
  have hV := relIndex_mul_relIndex (⊥ : Subgroup G)
    (V ⊓ centralizer (A : Set G)) V bot_le inf_le_left
  have hA := relIndex_mul_relIndex (⊥ : Subgroup G)
    (A ⊓ centralizer (V : Set G)) A bot_le inf_le_left
  simp only [relIndex_bot_left, inf_relIndex_left] at hV hA
  rw [hfirst, hindex, hcard] at hV
  have hp : 0 < (centralizer (V : Set G)).relIndex A :=
    Nat.pos_of_ne_zero ((centralizer (V : Set G)).subgroupOf A).index_ne_zero_of_finite
  apply (eq_of_le_of_card_ge hle ?_).symm
  nlinarith

omit [Finite G] in
/-- A normalizer-fixed mark in one subgroup centralizes the other factor. -/
theorem conjugate_mark_centralizes_of_normalizes
    (V : Subgroup G) {z g : G}
    (hN : normalizer (V : Set G) ≤ centralizer ({z} : Set G))
    (hVA : V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) :
    MulAut.conj g z ∈ centralizer (V : Set G) := by
  have hzN : z ∈ centralizer (normalizer (V : Set G) : Set G) := by
    intro n hn
    exact mem_centralizer_singleton_iff.mp (hN hn)
  have hm := map_centralizer_le_centralizer_image
    (normalizer (V : Set G) : Set G) (MulAut.conj g).toMonoidHom
    (mem_map_of_mem (MulAut.conj g).toMonoidHom hzN)
  rw [← coe_map, map_equiv_normalizer_eq] at hm
  exact centralizer_le hVA hm

/-- Weak closure and the balanced commutator calculation force equality of
the original subgroup with its mutually normalizing conjugate. -/
theorem conjugate_eq_of_weakly_closed_mark_and_balanced_indices
    (V : Subgroup G) [IsMulCommutative V] {z g : G}
    (hz : z ∈ V)
    (hN : normalizer (V : Set G) = centralizer ({z} : Set G))
    (hweak : ∀ a : G, MulAut.conj a z ∈ V → MulAut.conj a z = z)
    (hindex : (centralizer (V.map (MulAut.conj g).toMonoidHom : Set G)).relIndex V =
      (centralizer (V : Set G)).relIndex (V.map (MulAut.conj g).toMonoidHom))
    (hcomm : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ =
      V ⊓ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G))
    (hVA : V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) :
    V.map (MulAut.conj g).toMonoidHom = V := by
  have hc := (mutual_centralizers_eq_inf_of_balanced_indices V
    (V.map (MulAut.conj g).toMonoidHom)
    (card_map_of_injective (MulAut.conj g).injective).symm hindex hcomm hVA).2
  have hzg : MulAut.conj g z ∈ V ⊓ V.map (MulAut.conj g).toMonoidHom := by
    rw [← hc]
    exact ⟨mem_map_of_mem (MulAut.conj g).toMonoidHom hz,
      conjugate_mark_centralizes_of_normalizes V hN.le hVA⟩
  apply mem_normalizer_iff_map_conj_eq.mp
  rw [hN]
  exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp (hweak g hzg.1))
end Subgroup
