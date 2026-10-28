module
public import Theory.GroupTheory.PResidual.CoprimeKernelJoin
public import Theory.GroupTheory.PResidual.PrimeToMonotone

/-!
# Normalizer control for the cubic join through a coprime kernel

The intrinsic coprime-kernel residual calculation is transported into the
original ambient group. Thus every element normalizing QP also normalizes
VP: the latter is the embedded characteristic residual of QP. This is the
normality step for the actual two-A₃ product through a short block's possible
central two-cover in Aschbacher–Smith13.5.6, printed p.917.
-/

public section
open Subgroup
namespace Subgroup
variable {G:Type*} [Group G]

theorem embedded_primeToResidual_eq_join_of_coprime_kernel
    (p:ℕ) (Q V P:Subgroup G) (hVQ:V≤Q)
    (hVn:Q⊔P≤normalizer (V:Set G)) (hc:⁅P,Q⁆≤V)
    (hcop:Nat.Coprime p (Nat.card Q))
    (hg:primeToResidual p (V⊔P : Subgroup G)=⊤) :
    (primeToResidual p (Q⊔P : Subgroup G)).map (Q⊔P).subtype=V⊔P := by
  let R:=Q⊔P
  have hQR:Q≤R:=le_sup_left
  have hVR:V≤R:=hVQ.trans hQR
  have hPR:P≤R:=le_sup_right
  let Q':=Q.subgroupOf R
  let V':=V.subgroupOf R
  let P':=P.subgroupOf R
  let : V'.Normal:=normal_subgroupOf_of_le_normalizer hVn
  have hc':⁅P',Q'⁆≤V':=by
    apply (map_le_map_iff_of_injective R.subtype_injective).mp
    rw [map_commutator,map_subgroupOf_eq_of_le hPR,
      map_subgroupOf_eq_of_le hQR,map_subgroupOf_eq_of_le hVR]
    exact hc
  have hgen:Q'⊔P'=⊤:=by
    rw [←subgroupOf_sup hQR hPR]
    exact subgroupOf_self R
  have hcard:Nat.card Q'=Nat.card Q:=Nat.card_congr (subgroupOfEquivOfLe hQR).toEquiv
  have hX:V'⊔P'=(V⊔P).subgroupOf R:=(subgroupOf_sup hVR hPR).symm
  have hg':primeToResidual p (V'⊔P' : Subgroup R)=⊤:=by
    let e : (V⊔P : Subgroup G)≃*(V'⊔P' : Subgroup R):=
      (subgroupOfEquivOfLe (sup_le hVR hPR)).symm.trans (MulEquiv.subgroupCongr hX.symm)
    have he:=map_primeToResidual (p:=p) e
    rw [hg,map_top_of_surjective _ e.surjective] at he
    exact he.symm
  have hr:=primeToResidual_eq_sup_of_coprime_kernel p Q' V' P'
    (fun _ hx => hVQ hx) hc' hgen (hcard.symm ▸ hcop) hg'
  rw [hr,hX,map_subgroupOf_eq_of_le (sup_le hVR hPR)]

theorem normalizer_join_of_coprime_kernel
    (p:ℕ) (Q V P:Subgroup G) (hVQ:V≤Q)
    (hVn:Q⊔P≤normalizer (V:Set G)) (hc:⁅P,Q⁆≤V)
    (hcop:Nat.Coprime p (Nat.card Q))
    (hg:primeToResidual p (V⊔P : Subgroup G)=⊤) :
    normalizer ((Q⊔P : Subgroup G):Set G)≤normalizer ((V⊔P : Subgroup G):Set G) := by
  rw [←embedded_primeToResidual_eq_join_of_coprime_kernel p Q V P hVQ hVn hc hcop hg]
  exact normalizer_le_normalizer_characteristic_image (Q⊔P) (primeToResidual p (Q⊔P : Subgroup G))
end Subgroup
