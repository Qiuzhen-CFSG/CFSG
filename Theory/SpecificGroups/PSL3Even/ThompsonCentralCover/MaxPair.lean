module
public import Stellmacher.ElementaryAbelianMaxPair.CentralProduct
public import Theory.SpecificGroups.PSL3Even.ThompsonCentralCover
/-! # The two elementary maxima in a binary central linear cover
The actual component Sylow maps onto the standard unitriangular model.
Its elementary root-plane preimages supply two candidates. Under the source's
temporary elementary-centralizer assumption, maximum elementary subgroups
absorb that centralizer factor. The shared kernel belongs to both candidates,
so the central-product argument gives exactly two distinct maxima of S.
Source: Aschbacher--Smith 2.5.7, printed p.555, exceptional covering branch.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Matrix.PSL3Even.ThompsonCentralCover
open UnipotentGeometry PSL3.LinearThree
variable {G F:Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]
theorem maxFamily_pair_of_elementary_centralizer (K:Subgroup G) [K.Normal] [Group.IsPerfect K]
    (e:K⧸center K≃*PSL(3,F)) (hZ:IsPGroup 2 (center K))
    [IsElementaryAbelian 2 (center K)]
    (hlift:∀W:Subgroup PSL(3,F),IsElementaryAbelian 2 W →
      IsElementaryAbelian 2 (W.comap (projection K e)))
    {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n) (S:Sylow 2 G)
    [IsElementaryAbelian 2 (Stellmacher.elementaryAbelianMaxJ (S:Subgroup G)⊓centralizer (K:Set G):Subgroup G)] :
    ∃ V W:Subgroup G,V≠W ∧ Stellmacher.elementaryAbelianMaxSubgroups (S:Subgroup G)={V,W} := by
  let q:=projection K e
  let J:=Stellmacher.elementaryAbelianMaxJ (S:Subgroup G)
  let SK:=(S:Subgroup G)⊓K
  let C:=J⊓centralizer (K:Set G)
  obtain ⟨R,hR⟩:=S.exists_subgroupOf_eq_of_normal K
  let P:=R.mapSurjective (f:=q) (projection_surjective K e)
  let eU:U F≃*P:=(unipotentEquiv F).trans (Sylow.equiv (unipotentSylow F (by omega) hF) P)
  let r:SK→*P := {
    toFun x:=⟨q ⟨x,x.property.2⟩,mem_map_of_mem q
      (show (⟨x,x.property.2⟩:K)∈(R:Subgroup K) by rw [hR];exact x.property.1)⟩
    map_one':=by apply Subtype.ext;exact map_one q
    map_mul':=by
      intro x y
      apply Subtype.ext
      exact map_mul q (⟨x,x.property.2⟩:K) (⟨y,y.property.2⟩:K) }
  let qS:SK→*U F:=eU.symm.toMonoidHom.comp r
  have hr:Function.Surjective r:=by
    rintro ⟨y,hy⟩
    obtain ⟨k,hk,hke⟩:=hy
    have hkS:(k:G)∈(S:Subgroup G):=show k∈(S:Subgroup G).subgroupOf K from hR ▸ hk
    exact ⟨⟨k,⟨hkS,k.property⟩⟩,Subtype.ext hke⟩
  have hqS:Function.Surjective qS:=eU.symm.surjective.comp hr
  have hC:SK≤centralizer (C:Set G):=
    inf_le_right.trans (le_centralizer_iff.mp (show C≤centralizer (K:Set G) from inf_le_right))
  have hker:SK⊓C≤qS.ker.map SK.subtype:=by
    rintro x ⟨hx,hc⟩
    refine ⟨⟨x,hx⟩,?_,rfl⟩
    have hxZ:(⟨x,hx.2⟩:K)∈center K:=by
      apply mem_center_iff.mpr
      intro k
      exact Subtype.ext (hc.2 k k.property)
    have hxq:q ⟨x,hx.2⟩=1:=by
      change (⟨x,hx.2⟩:K)∈q.ker
      rw [projection_ker]
      exact hxZ
    change eU.symm (r ⟨x,hx⟩)=1
    rw [show r ⟨x,hx⟩=1 from Subtype.ext hxq,map_one]
  let j:U F→*PSL(3,F):=(P:Subgroup PSL(3,F)).subtype.comp eU.toMonoidHom
  have hqval (x:SK) : j (qS x)=q ⟨x,x.property.2⟩:=by
    change (eU (eU.symm (r x)):PSL(3,F))=_
    rw [eU.apply_symm_apply]
    rfl
  have hpre (V:Subgroup (U F)) [IsElementaryAbelian 2 V] :
      IsElementaryAbelian 2 (V.comap qS) := by
    let W:=V.map j
    let : IsElementaryAbelian 2 W:=IsElementaryAbelian.map j
    let : IsElementaryAbelian 2 (W.comap q):=hlift W inferInstance
    let a:(V.comap qS)→*(W.comap q) := {
      toFun x:=⟨⟨x.val,x.val.property.2⟩,by
        change q ⟨x.val,x.val.property.2⟩∈W
        rw [←hqval]
        exact mem_map_of_mem j x.property⟩
      map_one':=rfl
      map_mul' _ _:=rfl }
    have ha:Function.Injective a:=by
      intro x y h
      exact Subtype.ext (Subtype.ext (congrArg (fun z:W.comap q=>((z:K):G)) h))
    let : CommGroup (W.comap q):=IsMulCommutative.instCommGroup
    have hcomm:IsMulCommutative (V.comap qS):=IsMulCommutative.of_comm (fun x y=>ha (by
      rw [map_mul,map_mul,mul_comm]))
    refine { toIsMulCommutative:=hcomm
             exponent_dvd_p:=Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
    intro x
    apply ha
    rw [map_pow,map_one]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (W.comap q)) (a x)
  have hJ:J=SK⊔C:=thompson_eq_sylow_component_sup_centralizer K e hZ hlift hn hF S
  obtain ⟨hpair,hne⟩:=Stellmacher.maxFamily_pair_central_preimages (S:Subgroup G) SK C qS hqS
    hJ hC hker (V₁ F) (V₂ F)
    (fun he=>plane₁_not_le_plane₂ F he.le) ((card_V₁ F).trans (card_V₂ F).symm)
    (hpre (V₁ F)) (hpre (V₂ F)) (fun A hA=>by
      let :=hA
      exact elementary_le_plane F A)
  exact ⟨_,_,hne,hpair⟩
end Matrix.PSL3Even.ThompsonCentralCover
