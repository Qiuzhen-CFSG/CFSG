module
public import Theory.GroupTheory.TwoPlaneCover.MarkedFactor
/-! # Geometry of marked elementary planes
Full elementary plane preimages identify the actual centralizer and normal
plane, and their common order gives the intrinsic two-member maximum family.
Source application: Aschbacher--Smith 2.5.7.
-/
public section
open Subgroup
namespace Subgroup.TwoPlaneCover
variable {G Q:Type*} [Group G] [Group Q]
theorem marked_plane_centralizer
    (f:G→*Q) (K:Subgroup G) (P:Subgroup Q)
    (hf:Function.Surjective (f.comp K.subtype)) (hKC:K≤centralizer (f.ker:Set G))
    [IsMulCommutative (P.comap (f.comp K.subtype))]
    (hself:centralizer (P:Set Q)≤P) :
    centralizer (((P.comap (f.comp K.subtype)).map K.subtype):Set G)=
      (P.comap (f.comp K.subtype)).map K.subtype⊔f.ker := by
  let V:=(P.comap (f.comp K.subtype)).map K.subtype
  have hVP:V.map f=P:=by rw [Subgroup.map_map,map_comap_eq_self_of_surjective hf]
  have hlift:=Subgroup.ClassTwo.plane_lift_centralizes f K P hf hKC
  have he:centralizer (V:Set G)=P.comap f:=by
    apply le_antisymm ?_ hlift
    intro g hg
    apply hself
    intro p hp
    rw [←hVP] at hp
    obtain ⟨v,hv,rfl⟩:=hp
    exact (map_mul f v g).symm.trans ((congrArg f (hg v hv)).trans (map_mul f g v))
  change centralizer (V:Set G)=V⊔f.ker
  calc
    centralizer (V:Set G)=P.comap f:=he
    _=(V.map f).comap f:=congrArg (Subgroup.comap f) hVP.symm
    _=V⊔f.ker:=comap_map_eq f V

theorem marked_plane_normal
    (f:G→*Q) (K:Subgroup G) (P:Subgroup Q)
    (hf:Function.Surjective (f.comp K.subtype)) (hKC:K≤centralizer (f.ker:Set G))
    [P.Normal] : ((P.comap (f.comp K.subtype)).map K.subtype).Normal := by
  let A:=P.comap (f.comp K.subtype)
  let V:=A.map K.subtype
  have hKN:K≤normalizer (V:Set G):=by
    have hh:=A.le_normalizer_map K.subtype
    rw [normalizer_eq_top,←MonoidHom.range_eq_map,K.range_subtype] at hh
    exact hh
  have hCN:f.ker≤normalizer (V:Set G):=by
    apply (show f.ker≤centralizer (V:Set G) from ?_).trans (Subgroup.centralizer_le_normalizer _)
    apply le_centralizer_iff.mp
    rintro _ ⟨a,ha,rfl⟩
    exact hKC a.property
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [←Subgroup.ClassTwo.factor_sup_kernel f K hf]
  exact sup_le hKN hCN
end Subgroup.TwoPlaneCover
