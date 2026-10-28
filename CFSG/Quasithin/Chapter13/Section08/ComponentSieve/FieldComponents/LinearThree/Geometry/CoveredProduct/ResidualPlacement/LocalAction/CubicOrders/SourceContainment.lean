module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction.NaturalSetup
public import Theory.GroupTheory.PResidual.NormalSubgroup
/-!
# Containment of the source parabolic residual

The actual quotient LT/L is a two-group because L is normalized by the
supplied Sylow subgroup. Thus O²(N_LT(V₁)) lies in L without needing the
later covered factorization L₁=L₁,₊L₀.
Source: Aschbacher–Smith, Notation13.2.1, printed p.877.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction
variable {G : Type*} [Group G] [Finite G] {L T V P U : Subgroup G}
omit [Finite G] in
theorem NaturalSetup.one_le_local (d : NaturalSetup L T V P U) : one L T P ≤ L := by
  let J := L ⊔ T
  let A := L.subgroupOf J
  let B := T.subgroupOf J
  let : A.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer d.normalizes_L)
  have hB : IsPGroup 2 B := by
    change IsPGroup 2 (T.subgroupOf (L ⊔ T))
    rw [← d.sylow_eq]
    exact d.sylow.isPGroup'
  have hs : A ⊔ B = ⊤ := by
    change L.subgroupOf J ⊔ T.subgroupOf J = ⊤
    rw [← subgroupOf_sup (show L ≤ J from le_sup_left) (show T ≤ J from le_sup_right)]
    exact subgroupOf_self _
  have hq : IsPGroup 2 (J ⧸ A) := isPGroup_quotient_of_sup_eq_top A B hB hs
  have hr : pResidual 2 J ≤ A := sInf_le ⟨inferInstance,hq⟩
  have hm : residual J ≤ L := by
    have := map_mono (f := J.subtype) hr
    exact this.trans_eq (map_subgroupOf_eq_of_le (show L ≤ J from le_sup_left))
  exact (embedded_pResidual_mono 2 (show parabolic L T P ≤ J from inf_le_left)).trans hm
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction
