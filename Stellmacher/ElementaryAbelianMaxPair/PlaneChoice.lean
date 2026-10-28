module
public import Stellmacher.ElementaryAbelianMaxPair.MarkedGeneration
public import Theory.GroupTheory.SubgroupConjugation
public import Mathlib.GroupTheory.PGroup
/-! # Source plane choice from a marked pair
Self-centralizing model planes give the centralizer and index bounds for
every intrinsic maximum plane. When their full normalizers generate the
quotient component, one actual lifted plane normalizer escapes any subgroup
which does not contain that component. Sylow conjugacy supplies the marking.
Source application: Aschbacher--Smith 2.5.7, printed p.556.
-/
public section
open Subgroup
namespace Stellmacher
variable {G Q:Type*} [Group G] [Group Q] [Finite G]
omit [Finite G] in
theorem marked_plane_centralizer_bound
    (R K C:Subgroup G) (f:R→*Q)
    (hf:Function.Surjective (f.comp (K.subgroupOf R).subtype))
    (hk:f.ker=(R⊓C).subgroupOf R)
    (P:Subgroup Q) (hP:centralizer (P:Set Q)=P) :
    let V:=((P.comap (f.comp (K.subgroupOf R).subtype)).map (K.subgroupOf R).subtype).map R.subtype
    R⊓centralizer (V:Set G)≤V⊔C := by
  let A:=K.subgroupOf R
  let q:=f.comp A.subtype
  let V:=((P.comap q).map A.subtype).map R.subtype
  change R⊓centralizer (V:Set G)≤V⊔C
  intro r hr
  let r':R:=⟨r,hr.1⟩
  have hfr:f r'∈P:=by
    rw [←hP]
    intro p hp
    obtain ⟨a,ha⟩:=hf p
    have hav:(a.val:G)∈V:=mem_map_of_mem R.subtype (mem_map_of_mem A.subtype (show a∈P.comap q from (show q a∈P from ha.symm ▸ hp)))
    have hh:(a.val:R)*r'=r'*(a.val:R):=Subtype.ext (hr.2 _ hav)
    have he:=congrArg f hh
    simpa only [map_mul,←ha,MonoidHom.comp_apply,Subgroup.subtype_apply] using he
  obtain ⟨a,ha⟩:=hf (f r')
  have hav:(a.val:G)∈V:=mem_map_of_mem R.subtype (mem_map_of_mem A.subtype (show a∈P.comap q from (show q a∈P from ha.symm ▸ hfr)))
  have hrc:((a.val:R)⁻¹*r':R)∈f.ker:=by
    change f ((a.val:R)⁻¹*r')=1
    change f (a.val:R)=f r' at ha
    rw [map_mul,map_inv,ha,inv_mul_cancel]
  rw [hk] at hrc
  have hh:=mul_mem_sup hav hrc.2
  change (a.val:G)*((a.val:G)⁻¹*r)∈V⊔C at hh
  simpa only [mul_inv_cancel_left] using hh
end Stellmacher

namespace Stellmacher
variable {G:Type*} [Group G]
theorem pair_plane_normalizer_bounds
    (S K C V W:Subgroup G)
    (hpair:elementaryAbelianMaxSubgroups K={V,W}) (hne:V≠W)
    (hgen:V⊔W=K) (hSK:S≤normalizer (K:Set G))
    (hC:C≤centralizer (K:Set G)) :
    K⊔C≤normalizer (V:Set G) ∧
      (S⊓normalizer (V:Set G)).relIndex S≤2 := by
  have hJ:elementaryAbelianMaxJ K=K:=by
    change sSup (elementaryAbelianMaxSubgroups K)=K
    rw [hpair,sSup_insert,sSup_singleton,hgen]
  have hVK:V≤K:=hgen ▸ le_sup_left
  constructor
  · exact sup_le (hJ ▸ maxJ_le_normalizer_of_pair K V W hpair hne)
      ((hC.trans (centralizer_le hVK)).trans (Subgroup.centralizer_le_normalizer _))
  · rw [inf_relIndex_left]
    exact normalizer_relIndex_le_two_of_pair K V W S hpair hne hSK
end Stellmacher


open Subgroup
namespace Stellmacher
variable {G Q:Type*} [Group G] [Group Q] [Finite G]
theorem maxFamily_pair_of_relative_preimages
    (q:G→*Q) (hq:Function.Surjective q) (U P₀ P₁:Subgroup Q)
    (hP₀:P₀≤U) (hP₁:P₁≤U)
    [IsElementaryAbelian 2 (P₀.comap q)] [IsElementaryAbelian 2 (P₁.comap q)]
    (hcard:Nat.card P₀=Nat.card P₁)
    (hcover:∀A:Subgroup Q,IsElementaryAbelian 2 A→A≤U→A≤P₀∨A≤P₁) :
    elementaryAbelianMaxSubgroups (U.comap q)={P₀.comap q,P₁.comap q} := by
  have hsize:Nat.card (P₀.comap q)=Nat.card (P₁.comap q):=by
    rw [←IsElementaryAbelian.card_inf_ker_mul_card_map (P₀.comap q) q,
      ←IsElementaryAbelian.card_inf_ker_mul_card_map (P₁.comap q) q,
      inf_eq_right.mpr (P₀.ker_le_comap q),inf_eq_right.mpr (P₁.ker_le_comap q),
      map_comap_eq_self_of_surjective hq,map_comap_eq_self_of_surjective hq,hcard]
  apply maxFamily_eq_pair_of_cover (U.comap q) _ _ (comap_mono hP₀) (comap_mono hP₁) hsize
  intro A hA
  let :=hA.2.1
  exact (hcover (A.map q) (IsElementaryAbelian.map q)
    (map_le_iff_le_comap.mpr hA.1)).imp map_le_iff_le_comap.mp map_le_iff_le_comap.mp

theorem exists_maximum_escaping_normalizer_of_relative_planes
    (K M:Subgroup G) (hKM:¬K≤M) (q:K→*Q) (hq:Function.Surjective q)
    (U P₀ P₁:Subgroup Q) (hP₀:P₀≤U) (hP₁:P₁≤U)
    [IsElementaryAbelian 2 (P₀.comap q)] [IsElementaryAbelian 2 (P₁.comap q)]
    (hcard:Nat.card P₀=Nat.card P₁)
    (hcover:∀A:Subgroup Q,IsElementaryAbelian 2 A→A≤U→A≤P₀∨A≤P₁)
    (hgen:normalizer (P₀:Set Q)⊔normalizer (P₁:Set Q)=⊤) :
    ∃V∈elementaryAbelianMaxSubgroups ((U.comap q).map K.subtype),
      ¬K⊓normalizer (V:Set G)≤M := by
  classical
  let V₀:=(P₀.comap q).map K.subtype
  let V₁:=(P₁.comap q).map K.subtype
  have hpair:=maxFamily_pair_map K.subtype K.subtype_injective (U.comap q) _ _
    (maxFamily_pair_of_relative_preimages q hq U P₀ P₁ hP₀ hP₁ hcard hcover)
  have hv₀:V₀∈elementaryAbelianMaxSubgroups ((U.comap q).map K.subtype):=hpair.symm ▸ Set.mem_insert _ _
  have hv₁:V₁∈elementaryAbelianMaxSubgroups ((U.comap q).map K.subtype):=hpair.symm ▸ Set.mem_insert_of_mem _ (Set.mem_singleton _)
  by_cases h0:K⊓normalizer (V₀:Set G)≤M
  · refine ⟨V₁,hv₁,?_⟩
    intro h1
    have hN (P:Subgroup Q)
        (h:K⊓normalizer ((P.comap q).map K.subtype:Set G)≤M) :
        ((normalizer (P:Set Q)).comap q).map K.subtype≤M:=by
      rw [comap_normalizer_eq_of_surjective _ hq]
      exact (le_inf (map_subtype_le _) ((P.comap q).le_normalizer_map K.subtype)).trans h
    have hh:=sup_le (hN P₀ h0) (hN P₁ h1)
    rw [←Subgroup.map_sup,Subgroup.TwoPlaneCover.comap_sup_eq_top q hq _ _ hgen,
      ←MonoidHom.range_eq_map,K.range_subtype] at hh
    exact hKM hh
  · exact ⟨V₀,hv₀,h0⟩
end Stellmacher

namespace Stellmacher
open Subgroup
variable {G Q:Type*} [Group G] [Group Q] [Finite G] [Finite Q]
theorem exists_maximum_escaping_normalizer_of_sylow_planes
    (K M:Subgroup G) (hKM:¬K≤M) (q:K→*Q) (hq:Function.Surjective q)
    (hk:IsPGroup 2 q.ker) (P:Sylow 2 K) (U:Sylow 2 Q)
    (P₀ P₁:Subgroup Q) (hP₀:P₀≤U) (hP₁:P₁≤U)
    (hlift:∀W:Subgroup Q,IsElementaryAbelian 2 W→IsElementaryAbelian 2 (W.comap q))
    [IsElementaryAbelian 2 P₀] [IsElementaryAbelian 2 P₁]
    (hcard:Nat.card P₀=Nat.card P₁)
    (hcover:∀A:Subgroup Q,IsElementaryAbelian 2 A→A≤U→A≤P₀∨A≤P₁)
    (hgen:normalizer (P₀:Set Q)⊔normalizer (P₁:Set Q)=⊤) :
    ∃V∈elementaryAbelianMaxSubgroups ((P:Subgroup K).map K.subtype),
      ¬K⊓normalizer (V:Set G)≤M := by
  obtain ⟨g,hg⟩:=MulAction.exists_smul_eq Q (P.mapSurjective (f:=q) hq) U
  let q':K→*Q:=(MulAut.conj g).toMonoidHom.comp q
  have hq':Function.Surjective q':=(MulAut.conj g).surjective.comp hq
  have hk':q'.ker=q.ker:=MonoidHom.ker_comp_of_injective _ _ (MulAut.conj g).injective
  have himage:(P:Subgroup K).map q'=U:=by
    have hh:=congrArg Sylow.toSubgroup hg
    change ((P:Subgroup K).map q).map (MulAut.conj g).toMonoidHom=U at hh
    rwa [Subgroup.map_map] at hh
  have hU:(U:Subgroup Q).comap q'=P:=by
    rw [←himage]
    apply Subgroup.comap_map_eq_self
    exact (show IsPGroup 2 q'.ker from hk' ▸ hk).le_sylow_of_normal P
  have hp (W:Subgroup Q) [IsElementaryAbelian 2 W]:IsElementaryAbelian 2 (W.comap q'):=by
    change IsElementaryAbelian 2 ((W.comap (MulAut.conj g).toMonoidHom).comap q)
    apply hlift
    rw [comap_equiv_eq_map_symm']
    exact IsElementaryAbelian.map _
  let :=hp P₀
  let :=hp P₁
  have he:=exists_maximum_escaping_normalizer_of_relative_planes K M hKM q' hq'
    (U:Subgroup Q) P₀ P₁ hP₀ hP₁ hcard hcover hgen
  rwa [hU] at he
end Stellmacher

namespace Stellmacher
open Subgroup
variable {G Q:Type*} [Group G] [Group Q] [Finite G]
theorem marked_pair_plane_geometry
    (R K C S:Subgroup G) (hKR:K≤R) (hR:R=K⊔(R⊓C))
    (hSK:S≤normalizer (K:Set G)) (hC:C≤centralizer (K:Set G))
    (f:R→*Q) (hf:Function.Surjective (f.comp (K.subgroupOf R).subtype))
    (hk:f.ker=(R⊓C).subgroupOf R)
    (P₀ P₁:Subgroup Q)
    [IsElementaryAbelian 2 (P₀.comap (f.comp (K.subgroupOf R).subtype))]
    [IsElementaryAbelian 2 (P₁.comap (f.comp (K.subgroupOf R).subtype))]
    (hcard:Nat.card P₀=Nat.card P₁) (hne:P₀≠P₁)
    (hcover:∀A:Subgroup Q,IsElementaryAbelian 2 A→A≤P₀∨A≤P₁)
    (hgen:P₀⊔P₁=⊤) (hc₀:centralizer (P₀:Set Q)=P₀) (hc₁:centralizer (P₁:Set Q)=P₁) :
    ∀V∈elementaryAbelianMaxSubgroups K,
      R≤normalizer (V:Set G) ∧ C≤normalizer (V:Set G) ∧
      (S⊓normalizer (V:Set G)).relIndex S≤2 ∧
      R⊓centralizer (V:Set G)≤V⊔C := by
  let A:=K.subgroupOf R
  let q:=f.comp A.subtype
  let i:A→*G:=R.subtype.comp A.subtype
  have hi:Function.Injective i:=R.subtype_injective.comp A.subtype_injective
  have hr:i.range=K:=by
    rw [MonoidHom.range_comp,A.range_subtype,map_subgroupOf_eq_of_le hKR]
  obtain ⟨hp,hn⟩:=maxFamily_pair_of_marked_image q hf i hi P₀ P₁ hcard hne hcover
  rw [hr] at hp
  have hjoin:(P₀.comap q).map i⊔(P₁.comap q).map i=K:=by
    rw [←Subgroup.map_sup,Subgroup.TwoPlaneCover.comap_sup_eq_top q hf P₀ P₁ hgen,
      ←MonoidHom.range_eq_map,hr]
  have hb₀:=pair_plane_normalizer_bounds S K C _ _ hp hn hjoin hSK hC
  have hb₁:=pair_plane_normalizer_bounds S K C _ _ (hp.trans (Set.pair_comm _ _)) hn.symm
    (by rwa [sup_comm]) hSK hC
  have hRC:R≤K⊔C:=by rw [hR];exact sup_le le_sup_left (inf_le_right.trans le_sup_right)
  intro V hV
  rw [hp] at hV
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hV
  rcases hV with rfl|rfl
  · refine ⟨hRC.trans hb₀.1,le_sup_right.trans hb₀.1,hb₀.2,?_⟩
    simpa only [Subgroup.map_map,i] using marked_plane_centralizer_bound R K C f hf hk P₀ hc₀
  · refine ⟨hRC.trans hb₁.1,le_sup_right.trans hb₁.1,hb₁.2,?_⟩
    simpa only [Subgroup.map_map,i] using marked_plane_centralizer_bound R K C f hf hk P₁ hc₁
end Stellmacher
