module

public import Theory.GroupTheory.FullSylowSections
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Data.ZMod.Basic

/-!
# The center of C2 times D8

The center is elementary of order four and is therefore not cyclic.
A section retaining the whole Sylow order cannot have cyclic Sylow center.
This distinguishes the split Sylow of Aschbacher--Smith F.6.18(8)--(9)
from the rank-three linear and unitary Sylow groups, printed p.310.
-/

public section
open Subgroup
namespace Theory.GroupTheory

theorem split_dihedral_sixteen_center_not_cyclic :
    ¬ IsCyclic (center (Multiplicative (ZMod 2) × DihedralGroup 4)) := by
  intro h
  let := h
  have hc : Nat.card (center (Multiplicative (ZMod 2) × DihedralGroup 4)) = 4 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  have he : Monoid.exponent (center (Multiplicative (ZMod 2) × DihedralGroup 4)) ∣ 2 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by decide +kernel)
  rw [IsCyclic.exponent_eq_card, hc] at he
  norm_num at he

/-- The literal quotient of an original subgroup retains its noncyclic
Sylow center when its Sylow already uses all sixteen elements. -/
theorem not_cyclic_sylow_center_of_split_sixteen_section
    {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (T : Sylow 2 G) (eT : T ≃* (Multiplicative (ZMod 2) × DihedralGroup 4))
    (K : Subgroup G) (f : K →* H) (hf : Function.Surjective f)
    (P : Sylow 2 H) (hc : Nat.card P = 16) : ¬ IsCyclic (center P) := by
  intro h
  let := h
  have hT : Nat.card T = 16 := by
    rw [Nat.card_congr eT.toEquiv, Nat.card_prod, DihedralGroup.nat_card]
    norm_num
  obtain ⟨j⟩ := sylow_section_equiv_of_card_eq T K f hf P (hc.trans hT.symm)
  let a := centerCongr (j.trans eT)
  exact split_dihedral_sixteen_center_not_cyclic
    (isCyclic_of_surjective a.toMonoidHom a.surjective)

end Theory.GroupTheory
