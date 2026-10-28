module
public import Theory.SpecificGroups.SymplecticFour.SylowOuterRank
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.Thompson
public import Theory.GroupTheory.MaxElementaryImageComparison
public import Theory.GroupTheory.SylowNormalIntersection
/-! # Inner Thompson action for a normal binary symplectic component
The original action preserves the component Sylow and contains all its inner
actors. A root wing has order q³ and centralizes the action kernel. Maximum
elementary order therefore forces every maximum elementary actor image to have
order at least q³. The actual-Sylow outer bound makes every such image inner.
Source: Aschbacher--Smith 2.5.7, printed pp.554--555.
-/
public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace Theory.SpecificGroups.SymplecticFour.ThompsonInner
open CentralRootGeometry
variable {G F:Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]
noncomputable def action (K:Subgroup G) [K.Normal] (e:K≃*Sp F) : G→*MulAut (Sp F) :=
  (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal : G→*MulAut K)
omit [Finite G] [Finite F] [CharP F 2] in
theorem action_on_K (K:Subgroup G) [K.Normal] (e:K≃*Sp F) (k:K) :
    action K e k=MulAut.conj (e k) := by
  apply MulEquiv.ext
  intro y
  obtain ⟨x,rfl⟩ := e.surjective y
  change e (MulAut.conjNormal (k:G) (e.symm (e x)))=e k*e x*(e k)⁻¹
  rw [e.symm_apply_apply,←map_inv,←map_mul,←map_mul]
  rfl

omit [Finite G] [Finite F] [CharP F 2] in
/-- The actual conjugation kernel is the ambient component centralizer. -/
theorem action_ker_eq (K:Subgroup G) [K.Normal] (e:K≃*Sp F) :
    (action K e).ker = centralizer (K:Set G) := by
  ext a
  constructor
  · intro ha y hy
    have he : MulAut.conjNormal a=1 := (MulAut.congr e).injective
      (show MulAut.congr e (MulAut.conjNormal a)=MulAut.congr e 1 from by
        change (action K e) a=(MulAut.congr e) 1
        rw [map_one]
        exact ha)
    have hh := congrArg (fun b:MulAut K=>(b ⟨y,hy⟩:G)) he
    change a*y*a⁻¹=y at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  · intro ha
    change (MulAut.congr e) (MulAut.conjNormal a)=1
    rw [← (MulAut.congr e).map_one]
    congr 1
    apply MulEquiv.ext
    intro y
    apply Subtype.ext
    change a*(y:G)*a⁻¹=(y:G)
    rw [←ha y y.property,mul_inv_cancel_right]

omit [CharP F 2] in
private theorem actor_sylow (K:Subgroup G) [K.Normal] (e:K≃*Sp F)
    (S:Sylow 2 G) (R:Sylow 2 K)
    (hR:(R:Subgroup K)=(S:Subgroup G).subgroupOf K) :
    let P:=R.mapSurjective (f:=e.toMonoidHom) e.surjective
    ((P:Subgroup (Sp F)).map (MulAut.conj : Sp F→*MulAut (Sp F))≤
        (S:Subgroup G).map (action K e)) ∧
    (∀ a∈(S:Subgroup G).map (action K e),
      (P:Subgroup (Sp F)).map a.toMonoidHom=P) := by
  dsimp only
  constructor
  · rintro _ ⟨b,⟨k,hk,rfl⟩,rfl⟩
    refine ⟨(k:G),?_,action_on_K K e k⟩
    have hh : k∈(S:Subgroup G).subgroupOf K:=hR ▸ hk
    exact hh
  · rintro _ ⟨g,hg,rfl⟩
    apply eq_of_le_of_card_ge ?_ (by rw [card_map_of_injective (action K e g).injective])
    rintro _ ⟨b,⟨k,hk,rfl⟩,rfl⟩
    change e (MulAut.conjNormal g (e.symm (e k)))∈(R:Subgroup K).map e.toMonoidHom
    rw [e.symm_apply_apply]
    refine ⟨MulAut.conjNormal g k,?_,rfl⟩
    rw [hR]
    change g*(k:G)*g⁻¹∈(S:Subgroup G)
    have hkS : (k:G)∈(S:Subgroup G):=show k∈(S:Subgroup G).subgroupOf K from hR ▸ hk
    exact S.mul_mem (S.mul_mem hg hkS) (S.inv_mem hg)

theorem maxElementary_action_inner (K:Subgroup G) [K.Normal] (e:K≃*Sp F)
    {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n) (S:Sylow 2 G)
    (A:Subgroup G) (hA:A∈Stellmacher.elementaryAbelianMaxSubgroups (S:Subgroup G)) :
    A.map (action K e)≤MulAut.innerSubgroup (Sp F) := by
  let f:=action K e
  obtain ⟨R,hR⟩:=S.exists_subgroupOf_eq_of_normal K
  let P:=R.mapSurjective (f:=e.toMonoidHom) e.surjective
  have hrmap : (R:Subgroup K).map K.subtype=(S:Subgroup G)⊓K := by
    rw [hR,subgroupOf_map_subtype]
  let eU : unipotent (F:=F) ≃* ↥((S:Subgroup G)⊓K) :=
    ((Sylow.equiv (unipotentSylow hF (by omega)) P).trans
      ((R:Subgroup K).equivMapOfInjective e.toMonoidHom e.injective).symm).trans
      (((R:Subgroup K).equivMapOfInjective K.subtype K.subtype_injective).trans
        (MulEquiv.subgroupCongr hrmap))
  let j : unipotent (F:=F)→*G := ((S:Subgroup G)⊓K).subtype.comp eU.toMonoidHom
  have hj : Function.Injective j:=Subtype.val_injective.comp eU.injective
  have hjK (u:unipotent (F:=F)) : j u∈K:=(eU u).property.2
  have hfi : Function.Injective (f.comp j) := by
    intro a b hab
    have ha:=action_on_K K e (⟨j a,hjK a⟩:K)
    have hb:=action_on_K K e (⟨j b,hjK b⟩:K)
    change action K e (j a)=action K e (j b) at hab
    rw [ha,hb] at hab
    exact hj (congrArg (fun z:K=>(z:G)) (e.injective
      (DiagramAutomorphisms.InvolutionNormalForms.inner_injective hab)))
  let V:=(wing (F:=F) false).map j
  let : IsElementaryAbelian 2 (wing (F:=F) false):=wing_elementary false
  let : IsElementaryAbelian 2 V:=IsElementaryAbelian.map j
  have hV : V≤(S:Subgroup G) := by
    rintro _ ⟨u,hu,rfl⟩
    exact (eU u).property.1
  have hc : V≤centralizer (A⊓f.ker:Set G) := by
    rintro _ ⟨u,hu,rfl⟩ a ha
    have haC : a∈centralizer (K:Set G):=action_ker_eq K e ▸ ha.2
    exact (haC _ (hjK u)).symm
  have hv : Nat.card (V.map f)=(Nat.card F)^3 := by
    rw [show V.map f=(wing (F:=F) false).map (f.comp j) from Subgroup.map_map _ _ _]
    rw [card_map_of_injective hfi,card_wing]
  by_contra hout
  let : IsElementaryAbelian 2 A:=hA.2.1
  let : IsElementaryAbelian 2 (A.map f):=IsElementaryAbelian.map f
  obtain ⟨hPR,hRP⟩:=actor_sylow K e S R hR
  have hr:=SylowOuterRank.elementary_outer_rank_le hF hn P
    ((S:Subgroup G).map f) (S.isPGroup'.map f) hPR hRP
    (A.map f) inferInstance (map_mono hA.1) hout
  have htop : IsElementaryAbelian 2 (⊤:Subgroup (A.map f)) := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x=>
      Subtype.ext (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (A.map f)) x.val)) }
  have ha : Nat.card (A.map f)≤2^(2*n+1) := by
    have hb:=(primeRank_le_iff_elementary_card_le (A.map f)).mp hr ⊤ htop
    simpa only [Nat.card_congr Subgroup.topEquiv.toEquiv] using hb
  have hv':=Stellmacher.maxElementary_image_card_ge (S:Subgroup G) A V f hA hV hc
  rw [hv,hF,←pow_mul] at hv'
  have hpow : 2^(2*n+1)<2^(n*3):=Nat.pow_lt_pow_right (by decide) (by omega)
  exact (hpow.trans_le hv').not_ge ha

theorem thompson_action_inner (K:Subgroup G) [K.Normal] (e:K≃*Sp F)
    {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n) (S:Sylow 2 G) :
    (Stellmacher.elementaryAbelianMaxJ (S:Subgroup G)).map (action K e)≤
      MulAut.innerSubgroup (Sp F) := by
  apply map_le_iff_le_comap.mpr
  apply sSup_le
  intro A hA
  exact map_le_iff_le_comap.mp (maxElementary_action_inner K e hn hF S A hA)
end Theory.SpecificGroups.SymplecticFour.ThompsonInner
