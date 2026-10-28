module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.CentralCoreInvolutionSource
/-! # The ambient Sylow cannot normalize the component orbit
If T normalized K₀, then C_T(K₀) would be a nontrivial normal two-subgroup
of K₀T, since it contains the original O₂(H). The unique maximal two-local
would contain K₀T and hence the original local pair, a contradiction.
This is the final normalizer step of source 2.5.20; the preceding tightly
embedded argument must still prove that T normalizes K₀ in the nonnormal case.
Source: Aschbacher--Smith, printed p.564.
-/
public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory ComponentRefinement
variable {G:Type*} [Group G] [Finite G] {H L M:Subgroup G} {S:Sylow 2 H} {z:G}
theorem MathieuSourceSetup.ambient_sylow_not_normalize_component_orbit
    (c:MathieuSourceSetup H L M S z)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype) :
    ¬(c.T:Subgroup G)≤normalizer
      (componentOrbit L ((S:Subgroup H).map H.subtype):Set G) := by
  let Y:=(S:Subgroup H).map H.subtype
  let D:=componentOrbit L Y
  let T:Subgroup G:=c.T
  let X:=D⊔T
  let Q:=T⊓centralizer (D:Set G)
  intro hn
  have hTQ:T≤normalizer (Q:Set G):=by
    intro a ha b
    exact and_congr (T.le_normalizer ha b)
      (normalizer_le_normalizer_centralizer D (hn ha) b)
  have hDQ:D≤normalizer (Q:Set G):=
    (le_centralizer_iff.mp (show Q≤centralizer (D:Set G) from inf_le_right)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hQX:Q≤X:=inf_le_left.trans le_sup_right
  have hQcore:Q≤twoCore X:=le_pCoreIn_of_normalizes
    (c.T.isPGroup'.to_le (show Q≤T from inf_le_left)) hQX (sup_le hDQ hTQ)
  have hcore:twoCore X≠⊥:=by
    obtain ⟨t,ht,htC,_⟩:=MathieuSourceSetup.exists_central_core_involution c
    have he:=generated_orbit_core ⟨c.component_le,c.component⟩ S hgen
    rw [←he] at htC
    have htQ:t∈Q:=⟨c.sylow_lt.le htC.1,htC.2⟩
    intro heq
    have ht1:t=1:=mem_bot.mp (heq ▸ hQcore htQ)
    rw [ht1,orderOf_one] at ht
    omega
  have hXM:X≤M:=by
    apply core_overgroup_le_of_sylow c.T c.sylow_le c.unique hcore (c.T.subtype c.sylow_le)
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le c.sylow_le] using
      (show T≤X from le_sup_right)
  have hHX:H≤X:=by
    rw [hgen]
    exact sup_le ((le_componentOrbit L Y).trans le_sup_left) (c.sylow_lt.le.trans le_sup_right)
  exact c.pair.1.2.2.2.2 (c.pair.2.trans (hHX.trans hXM))
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
