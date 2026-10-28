module

public import Theory.GroupTheory.ElementaryIndexTwoNormalizer
public import Mathlib.GroupTheory.Sylow

/-!
# A Sylow-fixed elementary index-two factor is invariant

A non-elementary finite group has at most two elementary subgroups of
index two. Any acting group's orbit on such a factor therefore has size
at most two. If a Sylow two-subgroup fixes the factor, that orbit has odd
size, hence size one. The ambient version preserves the actual conjugation
homomorphism and the original subgroup.
This yields the index-two factor contradiction in Aschbacher--Smith13.7.11,
printed p.942, directly from the elementary intersection in13.7.10(3),(7).
-/

public section

open Subgroup
open scoped Pointwise
namespace Subgroup
variable {G N:Type*} [Group G] [Finite G] [Group N] [Finite N]
theorem elementary_index_two_fixed_of_sylow
    (ρ:G→*MulAut N) (T:Sylow 2 G) (W:Subgroup N)
    (hW:IsElementaryAbelian 2 W) (hWi:W.index=2)
    (hN:¬IsElementaryAbelian 2 N)
    (hT:∀t∈T,W.map (ρ t).toMonoidHom=W) :
    ∀g:G,W.map (ρ g).toMonoidHom=W := by
  classical
  let : MulAction G (Subgroup N):=MulAction.compHom (Subgroup N) ρ
  change ∀g:G,g • W=W
  by_cases hall:∀g:G,g • W=W
  · exact hall
  obtain ⟨b,hb⟩:=not_forall.mp hall
  let B:Subgroup N:=b • W
  let : IsElementaryAbelian 2 W:=hW
  have hB:IsElementaryAbelian 2 B := IsElementaryAbelian.map (ρ b).toMonoidHom
  have hBi:B.index=2 := (index_map_of_bijective (f:=(ρ b).toMonoidHom) (ρ b).bijective W).trans hWi
  have hcov:MulAction.orbit G W⊆({W,B}:Set (Subgroup N)) := by
    rintro C ⟨a,rfl⟩
    have ha:IsElementaryAbelian 2 (a • W:Subgroup N):=
      IsElementaryAbelian.map (ρ a).toMonoidHom
    have hai:(a • W:Subgroup N).index=2:=
      (index_map_of_bijective (f:=(ρ a).toMonoidHom) (ρ a).bijective W).trans hWi
    have eq_of_le (K:Subgroup N) (hKi:K.index=2) (hle:(a • W:Subgroup N)≤K) : a • W=K := by
      have hc:=(a • W:Subgroup N).card_mul_index
      have hkc:=K.card_mul_index
      rw [hai] at hc
      rw [hKi] at hkc
      exact eq_of_le_of_card_ge hle (by omega)
    rcases elementary_le_one_of_two_index_two W B hW hB hWi hBi (Ne.symm hb) hN
      (a • W) ha with hl|hr
    · exact Set.mem_insert_iff.mpr (Or.inl (eq_of_le W hWi hl))
    · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr (eq_of_le B hBi hr)))
  have hcard:(MulAction.orbit G W).ncard≤2:=
    (Set.ncard_le_ncard hcov (Set.toFinite _)).trans (le_of_eq (Set.ncard_pair (show W≠B from Ne.symm hb)))
  have hTS:(T:Subgroup G)≤MulAction.stabilizer G W:=hT
  have hnodvd:¬2∣(MulAction.stabilizer G W).index:=fun hd=>
    T.not_dvd_index (hd.trans (index_dvd_of_le hTS))
  rw [←MulAction.index_stabilizer] at hcard
  have hpos:0<(MulAction.stabilizer G W).index:=Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have he:(MulAction.stabilizer G W).index=1:=by omega
  have ht:=Subgroup.index_eq_one.mp he
  intro a
  exact (show a∈MulAction.stabilizer G W from ht.symm ▸ mem_top a)
end Subgroup
namespace Subgroup
open scoped Pointwise
variable {G:Type*} [Group G] [Finite G]
theorem normalizes_elementary_index_two_of_sylow
    (H A W:Subgroup G) (T:Sylow 2 H) (hWA:W≤A)
    (hW:IsElementaryAbelian 2 W) (hWi:W.relIndex A=2)
    (hA:¬IsElementaryAbelian 2 A) (hnA:H≤normalizer (A:Set G))
    (hT:∀t∈T,(t:G)∈normalizer (W:Set G)) :
    H≤normalizer (W:Set G) := by
  let ρ:H→*MulAut A:=A.normalizerMonoidHom.comp (inclusion hnA)
  let B:=W.subgroupOf A
  let : IsElementaryAbelian 2 W:=hW
  have hB:IsElementaryAbelian 2 B:=IsElementaryAbelian.subgroupOf hWA
  have hBm:B.map A.subtype=W:=map_subgroupOf_eq_of_le hWA
  have hm (a:H) : (B.map (ρ a).toMonoidHom).map A.subtype=
      W.map (MulAut.conj (a:G)).toMonoidHom := by
    have hc:A.subtype.comp (ρ a).toMonoidHom=(MulAut.conj (a:G)).toMonoidHom.comp A.subtype := by
      ext x
      rfl
    rw [map_map,hc,←map_map,hBm]
  have hfix:=elementary_index_two_fixed_of_sylow ρ T B hB hWi hA (fun t ht=>by
    apply map_injective A.subtype_injective
    rw [hm,hBm]
    exact mem_normalizer_iff_map_conj_eq.mp (hT t ht))
  intro a ha
  apply mem_normalizer_iff_map_conj_eq.mpr
  have he:=congrArg (Subgroup.map A.subtype) (hfix ⟨a,ha⟩)
  rw [hm,hBm] at he
  exact he
end Subgroup
