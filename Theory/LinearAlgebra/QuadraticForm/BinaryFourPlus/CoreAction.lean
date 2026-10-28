module
public import Theory.GroupTheory.WreathTwoResidual
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus
/-!
# Two-cores detected by the full binary plus orthogonal action

The order-72 actor has trivial two-core and Sylow two-subgroups of order eight.
Consequently a normal two-subgroup of a finite acting group is its full two-core
when its index in a Sylow subgroup is eight and the action is surjective.

Source: Aschbacher--Smith 2.4.29, printed p.545.
-/
public section
open Subgroup
namespace BinaryFourPlus

theorem twoCore_eq_bot : pCore 2 Wreath=⊥ := by
  let eSL := Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three
  let e := RegularWreathProduct.congr eSL (MulEquiv.refl C2)
  rw [←pCore_map_iso 2 e,Theory.GroupTheory.WreathTwoResidual.twoCore_eq_bot,Subgroup.map_bot]

theorem sylow_two_card_eight (T : Sylow 2 Wreath) : Nat.card T=8 := by
  have hc : Nat.card Wreath=72 :=
    (Nat.card_congr isometryEquivWreath.toEquiv).symm.trans card_isometrySubgroup
  rw [Sylow.card_eq_multiplicity,hc,show 72=2^3*9 by decide,
    Nat.factorization_mul (by decide) (by decide),Nat.factorization_pow]
  norm_num [Nat.prime_two.factorization,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬2∣9)]

variable {F : Type*} [Group F] [Finite F]
theorem twoCore_eq_of_surjective_sylow_index
    (f : F →* Wreath) (hf : Function.Surjective f)
    (T : Sylow 2 F) (E : Subgroup F) [E.Normal] (hE : IsPGroup 2 E)
    (hi : E.relIndex (T : Subgroup F)=8) : pCore 2 F=E := by
  have hEP : E≤pCore 2 F := le_sSup ⟨inferInstance,hE⟩
  have hpT : pCore 2 F≤(T : Subgroup F) := pCore_isPGroup.le_sylow_of_normal T
  have hET : E≤(T : Subgroup F) := hEP.trans hpT
  have hk : pCore 2 F≤f.ker := by
    have hn : ((pCore 2 F).map f).Normal := (inferInstance : (pCore 2 F).Normal).map f hf
    have hh : (pCore 2 F).map f≤pCore 2 Wreath := le_sSup ⟨hn,pCore_isPGroup.map f⟩
    rw [twoCore_eq_bot] at hh
    exact (Subgroup.map_eq_bot_iff _).mp (bot_unique hh)
  let ft := f.comp (T : Subgroup F).subtype
  have hc : Nat.card ft.range=8 := by
    rw [MonoidHom.range_comp,range_subtype]
    change Nat.card (T.mapSurjective hf)=8
    exact sylow_two_card_eight _
  have he : E.subgroupOf (T : Subgroup F) ≤ ft.ker := fun x hx=>hk (hEP hx)
  have hEq : E.subgroupOf (T : Subgroup F)=ft.ker := by
    apply eq_of_le_of_card_ge he
    have h1 := (E.subgroupOf (T : Subgroup F)).card_mul_index
    have h2 := ft.ker.card_mul_index
    change Nat.card (E.subgroupOf (T : Subgroup F))*E.relIndex (T : Subgroup F)=_ at h1
    rw [hi] at h1
    rw [index_ker,hc] at h2
    omega
  apply le_antisymm ?_ hEP
  intro x hx
  have hh : (⟨x,hpT hx⟩:T)∈ft.ker := hk hx
  rw [←hEq] at hh
  exact hh
end BinaryFourPlus
