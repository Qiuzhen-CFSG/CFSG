module
public import Theory.GroupTheory.MaxElementaryImageComparison
public import Theory.SpecificGroups.PSL3Even.OuterElementaryRank
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
public import Theory.SpecificGroups.PSL3Even.UnipotentGeometry.Transport
public import Theory.GroupTheory.AutomorphismTowerSimple
public import Theory.GroupTheory.SylowNormalIntersection
/-! # Maximum elementary actors on a normal binary PSL₃ component
An actual root plane in the component Sylow has order q² and centralizes the
kernel of conjugation. Maximum elementary order therefore forces every
actor image to have order at least q². The proved outer-actor rank bound n+1
contradicts this for n>1, so every such image, and hence J(S), acts inner.
Source: Aschbacher--Smith 2.5.7, printed p.555. -/
public section
open Subgroup
open scoped IsMulCommutative MatrixGroups
open scoped MatrixGroups
namespace Stellmacher
variable {G F:Type*} [Group G] [Finite G] [Field F] [Finite F]
/-- A maximum elementary subgroup has inner projective action once the
original Sylow contains a full root plane centralizing its action kernel. -/
theorem maxElementary_psl3_image_inner {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n)
    (S A V:Subgroup G) (f:G→*MulAut PSL(3,F))
    (hA:A∈elementaryAbelianMaxSubgroups S) (hV:V≤S)
    [IsElementaryAbelian 2 V]
    (hc:V≤centralizer (A⊓f.ker:Set G))
    (hv:Nat.card (V.map f)=(Nat.card F)^2) :
    A.map f≤MulAut.innerSubgroup PSL(3,F) := by
  by_contra hout
  let : IsElementaryAbelian 2 A := hA.2.1
  let : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map f
  have hr := Matrix.PSL3Even.OuterElementaryRank.rank_le_of_not_le_inner
    (show 0<n by omega) hF (A.map f) inferInstance hout
  let : CommGroup (A.map f) := IsMulCommutative.instCommGroup
  have hd := card_dvd_exponent_pow_rank' (A.map f)
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (A.map f)))
  have ha : Nat.card (A.map f)≤2^(n+1) :=
    (Nat.le_of_dvd (by positivity) hd).trans
      (pow_le_pow_right' (by decide : 1≤(2:ℕ)) hr)
  have hv' := maxElementary_image_card_ge S A V f hA hV hc
  rw [hv,hF,←pow_mul] at hv'
  have hpow : 2^(n+1)<2^(n*2) := Nat.pow_lt_pow_right (by decide) (by omega)
  exact (hpow.trans_le hv').not_ge ha
end Stellmacher
namespace Matrix.PSL3Even.ThompsonInner
open PSL3.LinearThree PSL3Even.UnipotentGeometry
variable {G F:Type*} [Group G] [Finite G] [Field F] [Finite F]
noncomputable def action (K:Subgroup G) [K.Normal] (e:K≃*PSL(3,F)) : G→*MulAut PSL(3,F) :=
  (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal : G→*MulAut K)
omit [Finite G] [Finite F] in
theorem action_on_K (K:Subgroup G) [K.Normal] (e:K≃*PSL(3,F)) (k:K) :
    action K e k=MulAut.conj (e k) := by
  apply MulEquiv.ext
  intro y
  obtain ⟨x,rfl⟩ := e.surjective y
  change e (MulAut.conjNormal (k:G) (e.symm (e x)))=e k*e x*(e k)⁻¹
  rw [e.symm_apply_apply,←map_inv,←map_mul,←map_mul]
  rfl

omit [Finite G] [Finite F] in
/-- The actual conjugation kernel is the ambient component centralizer. -/
theorem action_ker_eq (K:Subgroup G) [K.Normal] (e:K≃*PSL(3,F)) :
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

theorem maxElementary_action_inner (K:Subgroup G) [K.Normal] (e:K≃*PSL(3,F))
    {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n) (S:Sylow 2 G)
    (A:Subgroup G) (hA:A∈Stellmacher.elementaryAbelianMaxSubgroups (S:Subgroup G)) :
    A.map (action K e)≤MulAut.innerSubgroup PSL(3,F) := by
  let : CharP F 2 := by
    let := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (by simpa only [←Nat.card_eq_fintype_card] using hF)
  obtain ⟨R,hR⟩ := S.exists_subgroupOf_eq_of_normal K
  let R' := R.mapSurjective (f:=e.toMonoidHom) e.surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq PSL(3,F)
    (unipotentSylow F (show 0<n by omega) hF) R'
  let j : U F→*G := K.subtype.comp (e.symm.toMonoidHom.comp
    ((MulAut.conj g).toMonoidHom.comp (projective F)))
  let V := (V₁ F).map j
  have hV : V≤(S:Subgroup G) := by
    rintro _ ⟨u,hu,rfl⟩
    have hm : (MulAut.conj g) (projective F u)∈(R':Subgroup PSL(3,F)) := by
      have hh := congrArg Sylow.toSubgroup hg
      rw [←hh]
      exact mem_map_of_mem (MulAut.conj g).toMonoidHom ((projective_range F).le ⟨u,rfl⟩)
    obtain ⟨k,hk,hke⟩ := hm
    have he : e.symm ((MulAut.conj g) (projective F u))=k := by rw [←hke]; exact e.symm_apply_apply k
    change e.symm ((MulAut.conj g) (projective F u))∈(S:Subgroup G).subgroupOf K
    rw [he,←hR]
    exact hk
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map j
  have hc : V≤centralizer (A⊓(action K e).ker:Set G) := by
    rintro _ ⟨u,hu,rfl⟩ a ha
    have he : MulAut.conjNormal a=1 := (MulAut.congr e).injective
      (show MulAut.congr e (MulAut.conjNormal a)=MulAut.congr e 1 from by change (action K e) a=(MulAut.congr e) 1; rw [map_one]; exact ha.2)
    let k : K := e.symm ((MulAut.conj g) (projective F u))
    have hh := congrArg (fun b:MulAut K=>(b k:G)) he
    change a*(k:G)*a⁻¹=(k:G) at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  have hq : center PSL(3,F)=⊥ := by
    let := Atlas.sl_perfect (F:=F) 3 (by decide)
    exact Group.IsPerfect.center_quotient_center_eq_bot (SL(3,F))
  have hji : Function.Injective ((action K e).comp j) := by
    have he : (action K e).comp j = (MulAut.conj (G:=PSL(3,F))).comp
        ((MulAut.conj g).toMonoidHom.comp (projective F)) := by
      apply MonoidHom.ext
      intro u
      change action K e (e.symm ((MulAut.conj g) (projective F u)))=_
      rw [action_on_K,e.apply_symm_apply]
      rfl
    rw [he]
    exact (MulAut.conj_injective_of_center_eq_bot hq).comp
      ((MulAut.conj g).injective.comp (projective_injective F))
  have hv : Nat.card (V.map (action K e))=(Nat.card F)^2 := by
    rw [show V.map (action K e)=(V₁ F).map ((action K e).comp j) from Subgroup.map_map _ _ _]
    rw [←Nat.card_congr ((V₁ F).equivMapOfInjective _ hji).toEquiv]
    exact card_V₁ F
  exact Stellmacher.maxElementary_psl3_image_inner hn hF (S:Subgroup G) A V
    (action K e) hA hV hc hv

theorem thompson_action_inner (K:Subgroup G) [K.Normal] (e:K≃*PSL(3,F))
    {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n) (S:Sylow 2 G) :
    (Stellmacher.elementaryAbelianMaxJ (S:Subgroup G)).map (action K e)≤
      MulAut.innerSubgroup PSL(3,F) := by
  apply map_le_iff_le_comap.mpr
  apply sSup_le
  intro A hA
  exact map_le_iff_le_comap.mp (maxElementary_action_inner K e hn hF S A hA)
end Matrix.PSL3Even.ThompsonInner
