module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.SporadicModels.LocalConfiguration
public import Theory.Mathieu.M11.Properties.SylowTwo
public import Theory.Mathieu.M11.Properties.AutomorphismCentralizers
public import Theory.GroupTheory.SemidihedralNormalElementary
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# The M₁₁ branch of the sporadic rank-one sieve

All automorphisms of the actual M₁₁ carrier are inner. A normal copy with
trivial ambient centralizer is therefore the whole ambient group. Its Sylow
two-subgroups are semidihedral of order sixteen, whose only nontrivial normal
elementary subgroup has order two. This excludes the normal four-group of
15.3.43 without any further local-subgroup classification.

The proof transports the checked semidihedral presentation along actual
group equivalences. Source: Aschbacher--Smith, combined manuscript
(1 March 2004), the sporadic paragraph of 15.3.43, printed p.1140, and
1.1.5(3)(f), printed p.502.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.SporadicModels
variable {G : Type*} [Group G] [Finite G]

/-- A faithful normal M₁₁ cannot support the required normal four-group. -/
theorem LocalConfiguration.not_mathieu_eleven {K S M Y V : Subgroup G}
    (c : LocalConfiguration K S M Y V) (e : K ≃* Sporadic.Mathieu.M11) : False := by
  let : K.Normal := c.normal
  have hK : K = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨k, hk⟩ := Sporadic.Mathieu.automorphism_inner_of_equiv_m11 e
      (MulAut.conjNormal x)
    have hx : x = (k : G) :=
      MulAut.conjNormal_injective_of_centralizer_eq_bot K c.faithful
        (hk.trans MulAut.conjNormal_val.symm)
    exact hx ▸ k.property
  let eG : G ≃* Sporadic.Mathieu.M11 :=
    Subgroup.topEquiv.symm.trans ((MulEquiv.subgroupCongr hK.symm).trans e)
  obtain ⟨P, rfl⟩ := c.sylow
  obtain ⟨T, a, b, ha, hb, hc, hg⟩ := Sporadic.Mathieu.m11_exists_semidihedral_sylow
  let eP : P ≃* T :=
    (Subgroup.equivMapOfInjective (P : Subgroup G) eG.toMonoidHom eG.injective).trans
      ((P.mapSurjective eG.surjective).equiv T)
  have hn : M ≤ normalizer (V : Set G) :=
    (normal_subgroupOf_iff_le_normalizer c.plane_le_local).mp c.plane_normal
  let : (V.subgroupOf (P : Subgroup G)).Normal :=
    normal_subgroupOf_of_le_normalizer (c.sylow_le_local.trans hn)
  let : IsElementaryAbelian 2 V := c.plane_elementary
  let : IsElementaryAbelian 2 (V.subgroupOf (P : Subgroup G)) :=
    IsElementaryAbelian.subgroupOf c.plane_le_sylow
  let R : Subgroup T := (V.subgroupOf (P : Subgroup G)).map eP.toMonoidHom
  let : R.Normal := Subgroup.Normal.map inferInstance eP.toMonoidHom eP.surjective
  let : IsElementaryAbelian 2 R := IsElementaryAbelian.map eP.toMonoidHom
  have hcard : Nat.card R = 4 := by
    rw [Subgroup.card_map_of_injective eP.injective]
    exact (Nat.card_congr (subgroupOfEquivOfLe c.plane_le_sylow).toEquiv).trans c.plane_card
  have hR : R ≠ ⊥ := by
    intro h
    have := Subgroup.card_eq_one.mpr h
    omega
  have he := Semidihedral.normal_elementary_eq_of_order_sixteen a b ha hb hc hg R hR
  have hz : Nat.card (zpowers (a ^ 4)) = 2 := by
    rw [Nat.card_zpowers, orderOf_pow, ha]
    norm_num
  have hbad : 4 = 2 := hcard.symm.trans
    ((congrArg (fun U : Subgroup T => Nat.card U) he).trans hz)
  contradiction

/-- Exclude M₁₁ for the actual component quotient, keeping the original
component and its possible central cover in the reduction input. -/
theorem reduced_not_mathieu_eleven {Y S M I L V₁ V₂ : Subgroup G}
    (c : ReducedConfiguration Y S M I L V₁ V₂)
    (e : c.toComponentAction.image L ≃* Sporadic.Mathieu.M11) : False :=
  (localConfiguration_of_reduced c).not_mathieu_eleven e

end CFSG.Quasithin.Chapter15.Section03.RankOne.SporadicModels
