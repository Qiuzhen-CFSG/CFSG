module
public import Stellmacher.ElementaryAbelianMaxPair.CentralProduct
public import Theory.SpecificGroups.PSL3.RootPlaneGeometry
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.RankTwoGeneration
public import Theory.SpecificGroups.PSL3Even.ThompsonCentralCover
/-! # Root-plane normalizers generate the original linear component
The two actual projective root planes have point and line parabolics as
normalizers, and those parabolics generate PSL₃. Through a central cover,
elementary full plane preimages remain maximum factors of a Thompson
central product. If all ambient elementary-maximum normalizers lie in M,
both lifted parabolics lie in M and hence so does the original component.
The Sylow version constructs the standard-unipotent alignment and retains
the literal quotient map; no Borel or parabolic-placement premise is used.
Source: Aschbacher--Smith 2.5.7, printed p.555.
-/
public section
open Subgroup
open scoped MatrixGroups
namespace Matrix.PSL3Even.ThompsonCentralCover
open UnipotentGeometry PSL3.LinearThree PSL3.RootPlaneGeometry
variable {G F:Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]
omit [Finite F] [CharP F 2] in
private theorem rootPlane_as_projective (b:Bool) :
    rootPlane F b=(if b then V₁ F else V₂ F).map (projective F) := by
  rw [rootPlane,rootPlaneSL,Subgroup.map_map]
  rfl
omit [Finite F] in
private theorem elementary_rootPlane_cover (A:Subgroup PSL(3,F)) [IsElementaryAbelian 2 A]
    (hAU:A≤unipotent F) : A≤rootPlane F true ∨ A≤rootPlane F false := by
  let B:Subgroup (U F):=(A.subgroupOf (unipotent F)).map (unipotentEquiv F).symm.toMonoidHom
  let : IsElementaryAbelian 2 (A.subgroupOf (unipotent F)):=IsElementaryAbelian.subgroupOf hAU
  let : IsElementaryAbelian 2 B:=IsElementaryAbelian.map _
  have hle (V:Subgroup (U F)) (hB:B≤V) : A≤V.map (projective F):=by
    intro a ha
    let u:unipotent F:=⟨a,hAU ha⟩
    refine ⟨(unipotentEquiv F).symm u,hB (mem_map_of_mem _ (show u∈A.subgroupOf (unipotent F) from ha)),?_⟩
    change ((unipotentEquiv F) ((unipotentEquiv F).symm u):PSL(3,F))=a
    rw [MulEquiv.apply_symm_apply]
  simpa only [rootPlane_as_projective, Bool.true_eq_false, Bool.false_eq_true, if_true, if_false] using
    (elementary_le_plane F B).imp (hle (V₁ F)) (hle (V₂ F))

/-- If the two root-plane lifts are elementary, the ambient maximum-family
normalizers generate the original component. All maps are the supplied
literal quotient and subgroup embeddings. -/
theorem component_le_of_maxFamily_normalizers
    (S K C M:Subgroup G) (q:K→*PSL(3,F)) (hq:Function.Surjective q)
    (hU:(unipotent F).comap q=S.subgroupOf K)
    (hJ:Stellmacher.elementaryAbelianMaxJ S=(S⊓K)⊔C)
    (hC:C≤centralizer (K:Set G)) [IsElementaryAbelian 2 C]
    (hker:(S⊓K)⊓C≤q.ker.map K.subtype)
    (hlift:∀b:Bool,IsElementaryAbelian 2 ((rootPlane F b).comap q))
    (hM:∀A∈Stellmacher.elementaryAbelianMaxSubgroups S,normalizer (A:Set G)≤M) : K≤M := by
  let V (b:Bool):Subgroup G:=((rootPlane F b).comap q).map K.subtype
  have hVP (b:Bool) : rootPlane F b≤unipotent F:=
    map_mono (rootPlaneSL_le_unipotent F b)
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
    have hAU:(A.subgroupOf K).map q≤unipotent F:=by
      apply map_le_iff_le_comap.mpr
      rw [hU]
      exact fun x hx=> (hAS hx).1
    have hstep (b:Bool) (hh:(A.subgroupOf K).map q≤rootPlane F b) : A≤V b:=by
      intro a ha
      exact ⟨⟨a,hAK ha⟩,hh (mem_map_of_mem q ha),rfl⟩
    exact (elementary_rootPlane_cover _ hAU).imp (hstep true) (hstep false)
  have hcard:Nat.card (V true)=Nat.card (V false):=by
    have hc (b:Bool):Nat.card (rootPlane F b)=Nat.card F^2:=by
      rw [rootPlane_as_projective,card_map_of_injective (projective_injective F)]
      cases b
      · exact card_V₂ F
      · exact card_V₁ F
    let :=hlift true
    let :=hlift false
    dsimp only [V]
    rw [card_map_of_injective K.subtype_injective,card_map_of_injective K.subtype_injective,
      ←IsElementaryAbelian.card_inf_ker_mul_card_map ((rootPlane F true).comap q) q,
      ←IsElementaryAbelian.card_inf_ker_mul_card_map ((rootPlane F false).comap q) q,
      inf_eq_right.mpr ((rootPlane F true).ker_le_comap q),
      inf_eq_right.mpr ((rootPlane F false).ker_le_comap q),
      map_comap_eq_self_of_surjective hq,map_comap_eq_self_of_surjective hq,hc true,hc false]
  have hZV (b:Bool):(S⊓K)⊓C≤V b:=hker.trans (map_mono ((rootPlane F b).ker_le_comap q))
  have hpair:=Stellmacher.maxFamily_pair_central_product S (S⊓K) C (V true) (V false) hJ
    (inf_le_right.trans (le_centralizer_iff.mp hC)) (hVS true) (hVS false) hcover hcard (hZV true) (hZV false)
  have hpar (b:Bool):((parabolic F b).comap q).map K.subtype≤M:=by
    have hA:V b⊔C∈Stellmacher.elementaryAbelianMaxSubgroups S:=by
      rw [hpair]
      cases b
      · exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
      · exact Set.mem_insert _ _
    apply le_trans _ (hM _ hA)
    apply le_trans _ ((V b).normalizer_inf_normalizer_le_normalizer_sup C)
    refine le_inf ?_ ?_
    · have hn:(parabolic F b).comap q=normalizer ((rootPlane F b).comap q:Set K):=by
        rw [←normalizer_rootPlane F b,comap_normalizer_eq_of_surjective _ hq]
      rw [hn]
      exact ((rootPlane F b).comap q).le_normalizer_map K.subtype
    · exact (map_subtype_le _).trans ((le_centralizer_iff.mp hC).trans (Subgroup.centralizer_le_normalizer _))
  have htop:(parabolic F true).comap q⊔(parabolic F false).comap q=⊤:=by
    have hk:q.ker≤(parabolic F true).comap q⊔(parabolic F false).comap q:=
      ((parabolic F true).ker_le_comap q).trans le_sup_left
    rw [←Subgroup.comap_map_eq_self hk,Subgroup.map_sup,
      map_comap_eq_self_of_surjective hq,map_comap_eq_self_of_surjective hq]
    change ((pointParabolic F⊔lineParabolic F).comap q)=⊤
    rw [parabolics_sup_eq_top,comap_top]
  have hsup:=sup_le (hpar true) (hpar false)
  rw [←Subgroup.map_sup,htop,←MonoidHom.range_eq_map,K.range_subtype] at hsup
  exact hsup
/-- Sylow alignment discharges the standard-unipotent marking from the
actual central two-cover and the original Sylow subgroup. -/
theorem component_le_of_maxFamily_normalizers_of_sylow
    (S:Sylow 2 G) (K C M:Subgroup G) [K.Normal]
    (q:K→*PSL(3,F)) (hq:Function.Surjective q) (hk:IsPGroup 2 q.ker)
    {n:ℕ} (hn:0<n) (hF:Nat.card F=2^n)
    (hJ:Stellmacher.elementaryAbelianMaxJ (S:Subgroup G)=((S:Subgroup G)⊓K)⊔C)
    (hC:C≤centralizer (K:Set G)) [IsElementaryAbelian 2 C]
    (hker:((S:Subgroup G)⊓K)⊓C≤q.ker.map K.subtype)
    (hlift:∀W:Subgroup PSL(3,F),IsElementaryAbelian 2 W→IsElementaryAbelian 2 (W.comap q))
    (hM:∀A∈Stellmacher.elementaryAbelianMaxSubgroups (S:Subgroup G),normalizer (A:Set G)≤M) : K≤M := by
  obtain ⟨R,hR⟩:=S.exists_subgroupOf_eq_of_normal K
  let P:=R.mapSurjective (f:=q) hq
  obtain ⟨g,hg⟩:=MulAction.exists_smul_eq PSL(3,F) P (unipotentSylow F hn hF)
  let q':K→*PSL(3,F):=(MulAut.conj g).toMonoidHom.comp q
  have hq':Function.Surjective q':=(MulAut.conj g).surjective.comp hq
  have hk':q'.ker=q.ker:=MonoidHom.ker_comp_of_injective _ _ (MulAut.conj g).injective
  have himage:((S:Subgroup G).subgroupOf K).map q'=unipotent F:=by
    have hh:=congrArg Sylow.toSubgroup hg
    change ((R:Subgroup K).map q).map (MulAut.conj g).toMonoidHom=unipotent F at hh
    rw [Subgroup.map_map,hR] at hh
    exact hh
  have hU:(unipotent F).comap q'=(S:Subgroup G).subgroupOf K:=by
    rw [←himage]
    apply Subgroup.comap_map_eq_self
    exact hR ▸ (show IsPGroup 2 q'.ker from hk' ▸ hk).le_sylow_of_normal R
  have hplanes (b:Bool):IsElementaryAbelian 2 (rootPlane F b):=by
    rw [rootPlane_as_projective]
    cases b
    · exact IsElementaryAbelian.map (projective F) (A:=V₂ F)
    · exact IsElementaryAbelian.map (projective F) (A:=V₁ F)
  have hlift' (b:Bool):IsElementaryAbelian 2 ((rootPlane F b).comap q'):=by
    change IsElementaryAbelian 2 (((rootPlane F b).comap (MulAut.conj g).toMonoidHom).comap q)
    apply hlift
    rw [comap_equiv_eq_map_symm']
    let :=hplanes b
    exact IsElementaryAbelian.map _
  exact component_le_of_maxFamily_normalizers (S:Subgroup G) K C M q' hq' hU hJ hC
    (hk'.symm ▸ hker) hlift' hM
end Matrix.PSL3Even.ThompsonCentralCover
