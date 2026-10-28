module
public import Stellmacher.ElementaryAbelianMaxPair.CentralProduct
public import Theory.GroupTheory.SubgroupConjugation
/-! # Generation from two elementary-plane normalizers
A literal quotient of the component Sylow has two equally sized elementary
planes covering its elementary subgroups. Elementary full preimages, joined
to the elementary centralizer factor of J(S), are its maximum family. If the
two plane normalizers generate the quotient, containment of the ambient
maximum-family normalizers forces containment of the original component.
Source application: Aschbacher--Smith 2.5.7, p.555, symplectic root wings.
-/
public section
open Subgroup
namespace Stellmacher
variable {G Y:Type*} [Group G] [Finite G] [Group Y]
theorem component_le_of_two_plane_normalizers
    (S K C M:Subgroup G) (q:K→*Y) (hq:Function.Surjective q)
    (U:Subgroup Y) (D:Bool→Subgroup Y)
    (hDU:∀b,D b≤U)
    (hDcover:∀A:Subgroup Y,IsElementaryAbelian 2 A→A≤U→A≤D true∨A≤D false)
    (hDcard:Nat.card (D true)=Nat.card (D false))
    (hDgen:normalizer (D true:Set Y)⊔normalizer (D false:Set Y)=⊤)
    (hU:U.comap q=S.subgroupOf K)
    (hJ:Stellmacher.elementaryAbelianMaxJ S=(S⊓K)⊔C)
    (hC:C≤centralizer (K:Set G)) [IsElementaryAbelian 2 C]
    (hker:(S⊓K)⊓C≤q.ker.map K.subtype)
    (hlift:∀b:Bool,IsElementaryAbelian 2 ((D b).comap q))
    (hM:∀A∈Stellmacher.elementaryAbelianMaxSubgroups S,normalizer (A:Set G)≤M) : K≤M := by
  let V (b:Bool):Subgroup G:=((D b).comap q).map K.subtype
  have hVP (b:Bool) : D b≤U:=hDU b
  have hVS (b:Bool) : V b≤S⊓K:=by
    rintro _ ⟨x,hx,rfl⟩
    exact ⟨show x∈S.subgroupOf K from hU ▸ hVP b hx,x.property⟩
  have hVelem (b:Bool):IsElementaryAbelian 2 (V b):=by
    let :=hlift b
    exact IsElementaryAbelian.map K.subtype
  let : IsElementaryAbelian 2 (V true):=hVelem true
  let : IsElementaryAbelian 2 (V false):=hVelem false
  have hcover (A:Subgroup G) (hA:IsElementaryAbelian 2 A) (hAS:A≤S⊓K) :
      A≤V true ∨ A≤V false:=by
    let :=hA
    have hAK:A≤K:=hAS.trans inf_le_right
    let : IsElementaryAbelian 2 (A.subgroupOf K):=IsElementaryAbelian.subgroupOf hAK
    let : IsElementaryAbelian 2 ((A.subgroupOf K).map q):=IsElementaryAbelian.map q
    have hAU:(A.subgroupOf K).map q≤U:=by
      apply map_le_iff_le_comap.mpr
      rw [hU]
      exact fun x hx=> (hAS hx).1
    have hstep (b:Bool) (hh:(A.subgroupOf K).map q≤D b) : A≤V b:=by
      intro a ha
      exact ⟨⟨a,hAK ha⟩,hh (mem_map_of_mem q ha),rfl⟩
    exact (hDcover _ inferInstance hAU).imp (hstep true) (hstep false)
  have hcard:Nat.card (V true)=Nat.card (V false):=by
    let :=hlift true
    let :=hlift false
    dsimp only [V]
    rw [card_map_of_injective K.subtype_injective,card_map_of_injective K.subtype_injective,
      ←IsElementaryAbelian.card_inf_ker_mul_card_map ((D true).comap q) q,
      ←IsElementaryAbelian.card_inf_ker_mul_card_map ((D false).comap q) q,
      inf_eq_right.mpr ((D true).ker_le_comap q),
      inf_eq_right.mpr ((D false).ker_le_comap q),
      map_comap_eq_self_of_surjective hq,map_comap_eq_self_of_surjective hq,hDcard]
  have hZV (b:Bool):(S⊓K)⊓C≤V b:=hker.trans (map_mono ((D b).ker_le_comap q))
  have hpair:=maxFamily_pair_central_product S (S⊓K) C (V true) (V false) hJ
    (inf_le_right.trans (le_centralizer_iff.mp hC)) (hVS true) (hVS false) hcover hcard (hZV true) (hZV false)
  have hpar (b:Bool):((normalizer (D b:Set Y)).comap q).map K.subtype≤M:=by
    have hA:V b⊔C∈Stellmacher.elementaryAbelianMaxSubgroups S:=by
      rw [hpair]
      cases b
      · exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
      · exact Set.mem_insert _ _
    apply le_trans _ (hM _ hA)
    apply le_trans _ ((V b).normalizer_inf_normalizer_le_normalizer_sup C)
    refine le_inf ?_ ?_
    · have hn:(normalizer (D b:Set Y)).comap q=normalizer ((D b).comap q:Set K):=by
        rw [comap_normalizer_eq_of_surjective _ hq]
      rw [hn]
      exact ((D b).comap q).le_normalizer_map K.subtype
    · exact (map_subtype_le _).trans ((le_centralizer_iff.mp hC).trans (Subgroup.centralizer_le_normalizer _))
  have htop:(normalizer (D true:Set Y)).comap q⊔(normalizer (D false:Set Y)).comap q=⊤:=by
    have hk:q.ker≤(normalizer (D true:Set Y)).comap q⊔(normalizer (D false:Set Y)).comap q:=
      ((normalizer (D true:Set Y)).ker_le_comap q).trans le_sup_left
    rw [←Subgroup.comap_map_eq_self hk,Subgroup.map_sup,
      map_comap_eq_self_of_surjective hq,map_comap_eq_self_of_surjective hq]
    rw [hDgen,comap_top]
  have hsup:=sup_le (hpar true) (hpar false)
  rw [←Subgroup.map_sup,htop,←MonoidHom.range_eq_map,K.range_subtype] at hsup
  exact hsup
end Stellmacher
