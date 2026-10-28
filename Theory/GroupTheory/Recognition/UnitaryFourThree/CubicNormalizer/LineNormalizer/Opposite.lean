module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicNormalizer.LineNormalizer.Data
/-!
# The opposite reflected cubic line

The same two original reflections can be exchanged. The original plane
containing the second reflection supplies its simultaneous marking; the
full normalizer theorem applies to this complementary fixed line as well.
Source: Aschbacher, Sporadic Groups (1994),45.7–45.8,pp.245–246.
-/
public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair
variable {G:Type*} [Group G] [Finite G] {z:G}
theorem reflected_actors_not_core (R:RootPair z) (h:IsType z)
    (P:Sylow 3 (centralizer z))
    (m:CubicNormalizer.ReflectedMarking z ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (ht:m.t∈R.cubicSylow ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (hs:m.s∈R.cubicSylow ((P:Subgroup (centralizer z)).map (centralizer z).subtype)) : m.t∉core z∧m.s∉core z:=by
  let X:=(P:Subgroup (centralizer z)).map (centralizer z).subtype
  have hzC:zpowers z≤Subgroup.centralizer ((X⊓Subgroup.centralizer ({m.t}:Set G):Subgroup G):Set G):=
    zpowers_le.mpr (fun x hx=>mem_centralizer_singleton_iff.mp ((map_subtype_le _) hx.1))
  have htc:m.t∉zpowers z:=by
    intro hh
    have he:zpowers m.t≤zpowers z:=zpowers_le.mpr hh
    have hc:Nat.card (zpowers z⊔zpowers m.t:Subgroup G)=4:=(h.reflected_four P m).2
    rw[sup_eq_left.mpr he,Nat.card_zpowers,h.involution] at hc
    omega
  have hi:core z⊓R.cubicSylow X=zpowers z:=R.cubicSylow_inf_core h X (h.cubic_sylow_image_card P) (map_subtype_le _)
  exact ⟨fun hh=>htc (hi ▸ ⟨hh,ht⟩),fun hh=>m.s_not_centralizes_fixed (hzC (hi ▸ ⟨hh,hs⟩))⟩

theorem opposite_line_normalizer_data (R:RootPair z) (h:IsType z)
    (P:Sylow 3 (centralizer z))
    (m:CubicNormalizer.ReflectedMarking z ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (ht:m.t∈R.cubicSylow ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (hs:m.s∈R.cubicSylow ((P:Subgroup (centralizer z)).map (centralizer z).subtype)) :
    let X:=(P:Subgroup (centralizer z)).map (centralizer z).subtype
    let B:=X⊓Subgroup.centralizer ({m.s}:Set G)
    let V:=CubicNormalizer.oddKernel X
    let K:=normalizer (B:Set G)
    Nat.card B=3 ∧ V≤K ∧ K≤normalizer (V:Set G) ∧ V.relIndex K=24 ∧
      ∃f:K→*Equiv.Perm (Fin 4),Function.Surjective f ∧ f.ker=V.subgroupOf K := by
  let X:=(P:Subgroup (centralizer z)).map (centralizer z).subtype
  have hX:Nat.card X=9:=h.cubic_sylow_image_card P
  have hXH:X≤centralizer z:=map_subtype_le _
  obtain ⟨htQ,hsQ⟩:=R.reflected_actors_not_core h P m ht hs
  have hs2:m.s^2=1:=m.s_order ▸ pow_orderOf_eq_one m.s
  have ht2:m.t^2=1:=m.t_order ▸ pow_orderOf_eq_one m.t
  have hsS:m.s∉zpowers z⊔zpowers m.t:=by
    intro hh
    have he:=R.reflected_four_eq_sylow_fixed h P m ht hs
    exact m.s_not_centralizes_fixed ((he.symm ▸ hh).2)
  have hts:m.t*m.s*m.t⁻¹=m.s*z:=R.outside_reflection_conjugation h P m ht hs m.s hs hs2 hsS
  have hB:Nat.card (X⊓Subgroup.centralizer ({m.s}:Set G):Subgroup G)=3:=
    R.cubic_involution_fixed_card h X hX hXH m.s hs hs2 hsQ
  let m':CubicNormalizer.ReflectedMarking z X:=
    { t:=m.s,s:=m.t,t_order:=m.s_order,s_order:=m.t_order,
      t_normalizes:=m.s_normalizes,s_normalizes:=m.t_normalizes,
      zt_commute:=(mem_centralizer_singleton_iff.mp (R.T_le_centralizer hs.1)).symm,
      t_fused:=h.involution_fused m.s m.s_order,reflection_conjugation:=hts,
      common_fixed_card:=hB,
      rotation_inverts:=R.cubic_reflection_rotation_inverts h X hX hXH m.s m.t hs ht hs2 ht2 hsQ htQ hts }
  have hsR:m.s∈R.R:=(R.involution_mem_R_or_core h m.s hs.1 m.s_order).resolve_right hsQ
  let : IsElementaryAbelian 2 (zpowers m.s):=IsElementaryAbelian.zpowers_of_pow_eq_one hs2
  obtain ⟨A,hSA,hAT,hAE,hAc⟩:=R.elementary_in_R_le_plane h (zpowers m.s) (zpowers_le.mpr hsR)
  have hA:A≤R.T∧IsElementaryAbelian 2 A∧Nat.card A=16:=⟨hAT,hAE,hAc⟩
  have hswap:=R.T_involution_swaps_core_factors h m.s hs.1 hs2 hsQ
  have hlocal:=h.reflected_line_normalizer_eq P m' hswap.1 hswap.2
  have hh:=R.reflected_line_normalizer_data h P m' A hA (hSA (mem_zpowers m.s)) hs ht
    (R.cubicSylow_normalizes_plane h X A hA) hlocal
  exact ⟨hB,hh⟩
end Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair
