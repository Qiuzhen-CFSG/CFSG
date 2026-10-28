module

public import Theory.GroupTheory.FullSylowSections
public import Mathlib.Data.ZMod.Basic

/-!
# Elementary sections under C2 times D8

An elementary section using all sixteen Sylow elements would inherit the
whole ambient Sylow group. Its order-four rotation gives a contradiction.
This is the PSL2(16) exclusion in Aschbacher--Smith F.6.18, printed p.310.
-/

public section
open Subgroup
namespace Theory.GroupTheory

theorem not_elementary_sixteen_sylow_section
    {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (T : Sylow 2 G) (eT : T ≃* (Multiplicative (ZMod 2) × DihedralGroup 4))
    (K : Subgroup G) (f : K →* H) (hf : Function.Surjective f)
    (P : Sylow 2 H) [IsElementaryAbelian 2 P] (hc : Nat.card P = 16) : False := by
  have hT : Nat.card T = 16 := by
    rw [Nat.card_congr eT.toEquiv, Nat.card_prod, DihedralGroup.nat_card]
    norm_num
  obtain ⟨j⟩ := sylow_section_equiv_of_card_eq T K f hf P (hc.trans hT.symm)
  let a := j.trans eT
  let : IsElementaryAbelian 2 (Multiplicative (ZMod 2) × DihedralGroup 4) :=
    IsElementaryAbelian.of_surjective a.toMonoidHom a.surjective
  have hr := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 (Multiplicative (ZMod 2) × DihedralGroup 4))
    (1, DihedralGroup.r 1)
  exact (by decide : ((1, DihedralGroup.r 1) : Multiplicative (ZMod 2) × DihedralGroup 4) ^ 2 ≠ 1) hr

end Theory.GroupTheory
