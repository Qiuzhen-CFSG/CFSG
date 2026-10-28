module

public import Theory.GroupTheory.SolvableNormalAbelian
public import Theory.GroupAction.MinimalNormal
public import Mathlib.GroupTheory.Sylow

/-!
# Minimal normal subgroups inside a solvable normal subgroup

A nontrivial solvable normal subgroup contains a minimal nontrivial normal
subgroup. Its last nontrivial derived subgroup is characteristic and abelian,
so minimality makes the whole subgroup abelian. A nontrivial Sylow subgroup
is then characteristic, and minimality makes it the whole subgroup as well.
Thus the minimal normal subgroup is an abelian p-group for some prime p.

Source application: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.1.10(8), printed p.212. The application needs abelianness and prime-power
order; no choice of an elementary-abelian structure is required.
-/

open Subgroup
open scoped IsMulCommutative

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A nontrivial solvable normal subgroup contains an abelian minimal normal p-subgroup. -/
public theorem exists_minimal_normal_abelian_pGroup (Y : Subgroup G) [Y.Normal]
    [Group.IsSolvable Y] (hY : Y ≠ ⊥) :
    ∃ (U : Subgroup G) (p : ℕ), U.Normal ∧ U ≠ ⊥ ∧ U ≤ Y ∧
      p.Prime ∧ IsMulCommutative U ∧ IsPGroup p U ∧
      ∀ V : Subgroup G, V.Normal → V ≤ U → V = ⊥ ∨ V = U := by
  obtain ⟨U, ⟨hUn, hUne⟩, hUY, hmin⟩ := exists_minimal_subgroup_of_mem_le
    (fun V : Subgroup G => V.Normal ∧ V ≠ ⊥) Y ⟨inferInstance, hY⟩
  let _ : U.Normal := hUn
  let _ : Nontrivial U := (nontrivial_iff_ne_bot U).mpr hUne
  let _ : Group.IsSolvable U :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective hUY)
  obtain ⟨C, hCchar, hCcomm, hCne⟩ := Group.exists_nontrivial_abelian_characteristic U
  let _ := hCchar
  let _ := hCcomm
  have hCeq : C.map U.subtype = U := hmin _
    ⟨inferInstance, fun he => hCne ((C.map_eq_bot_iff_of_injective U.subtype_injective).mp he)⟩
    (map_subtype_le _)
  have hUcomm : IsMulCommutative U := hCeq ▸ (map_isMulCommutative C U.subtype)
  let _ := hUcomm
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd
    (show Nat.card U ≠ 1 from ne_of_gt Finite.one_lt_card)
  let _ : Fact p.Prime := ⟨hp⟩
  let S : Sylow p U := Classical.choice inferInstance
  have hSn : (S : Subgroup U).Normal := inferInstance
  let _ : (S : Subgroup U).Characteristic := S.characteristic_of_normal hSn
  have hSeq : (S : Subgroup U).map U.subtype = U := hmin _
    ⟨inferInstance, fun he => S.ne_bot_of_dvd_card hpd
      (((S : Subgroup U).map_eq_bot_iff_of_injective U.subtype_injective).mp he)⟩
    (map_subtype_le _)
  refine ⟨U, p, hUn, hUne, hUY, hp, hUcomm, hSeq ▸ S.isPGroup'.map U.subtype, ?_⟩
  intro V hV hVU
  by_cases he : V = ⊥
  · exact Or.inl he
  · exact Or.inr (hmin V ⟨hV, he⟩ hVU)
end Subgroup

