module
public import Theory.SpecificGroups.PSL2.BinarySylowEmbedding
public import Theory.SpecificGroups.Triality.BinaryParabolicThreeRank
public import Theory.SpecificGroups.Triality.TwoLocalCover
public import Theory.SpecificGroups.Triality.InvolutionTwoComponents
public import Theory.SpecificGroups.Triality.StandardTwoRank.Sylow
public import Theory.GroupAction.InnerInvolutionGeometry
public import Theory.GroupTheory.RankOneSylowExtension
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupAction.AutomorphismFixedTransport
/-!
# The two triality involution rows for source components

An inner fixed group embeds in a genuine full parabolic by the two-local
cover theorem. A simple perfect subgroup lies in its local factor and survives
the solvable two-core quotient, so it embeds in binary PSL₂ and has commutative
Sylow two-subgroups. An outer fixed group is the genuine smaller triality
carrier. Simplicity makes an ordinary component the whole fixed group, with
its actual image and exact two-rank 5m retained, including m = 1.

Source: Aschbacher–Smith 2.5.19, p.561, and 16.1.4(1,4), p.1171.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Triality.Standard.InvolutionFixedComponents
open Parabolics

private theorem parabolic_perfect_image_le_local {K:Type*} [_root_.Group K] [Group.IsPerfect K]
    (P:Parameters) (hp:P.prime=2) (b:Node) (f:K→*parabolic P b) :
    f.range≤(localFactor P b).subgroupOf (parabolic P b) := by
  let N:=(localFactor P b).subgroupOf (parabolic P b)
  let :=parabolic_quotient_isCyclic P hp b
  have hderived:commutator (parabolic P b)≤N:=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le (N:=N)).mp inferInstance
  let : Group.IsPerfect f.range:=Group.IsPerfect.range f
  apply le_trans ?_ hderived
  rw [←commutator_eq_self (H:=f.range)]
  exact commutator_mono le_top le_top

/-- A simple perfect subgroup of an actual full parabolic has commutative Sylow two-subgroups. -/
theorem sylow_commutative_of_simple_parabolic_embedding
    {K:Type*} [_root_.Group K] [Finite K] [IsSimpleGroup K] [Group.IsPerfect K]
    (P:Parameters) (hp:P.prime=2) (b:Node)
    (f:K→*parabolic P b) (hf:Function.Injective f) (S:Sylow 2 K) :
    IsMulCommutative S := by
  let N:=(localFactor P b).subgroupOf (parabolic P b)
  have hN:=parabolic_perfect_image_le_local P hp b f
  let fN:K→*N:=f.codRestrict N (fun x=>hN ⟨x,rfl⟩)
  have hfN:Function.Injective fN:=fun x y h=>hf (congrArg Subtype.val h)
  let e:N≃*localFactor P b:=subgroupOfEquivOfLe (localFactor_le_parabolic P b)
  let j:=e.toMonoidHom.comp fN
  have hj:Function.Injective j:=e.injective.comp hfN
  let : Group.IsNilpotent (pCore 2 (localFactor P b)):=pCore_isNilpotent
  have hq:=Subgroup.RankOneSylowExtension.simple_quotient_injective
    (Group.IsPerfect.not_isSolvable K) j hj (pCore 2 (localFactor P b))
  let q:=(QuotientGroup.mk' (pCore 2 (localFactor P b))).comp j
  cases b with
  | arms =>
    let : CharP (ExtensionField P) 2:=hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
    exact Theory.PSL2.binary_sylow_commutative_of_injective
      ((localFactorArmsQuotientEquivPSL2 P hp).toMonoidHom.comp q)
      ((localFactorArmsQuotientEquivPSL2 P hp).injective.comp hq) S
  | central =>
    let : CharP (GaloisField P.prime P.exponent) 2:=hp ▸
      inferInstanceAs (CharP (GaloisField P.prime P.exponent) P.prime)
    exact Theory.PSL2.binary_sylow_commutative_of_injective
      ((localFactorCentralQuotientEquivPSL2 P hp).toMonoidHom.comp q)
      ((localFactorCentralQuotientEquivPSL2 P hp).injective.comp hq) S

/-- The original inner fixed group embeds in a full parabolic, with no containment premise. -/
theorem sylow_commutative_of_simple_inner_fixed_embedding
    {K:Type*} [_root_.Group K] [Finite K] [IsSimpleGroup K] [Group.IsPerfect K]
    (n:ℕ) (hn:0<n) (a:MulAut (BinaryCarrier n hn)) (ha:orderOf a=2)
    (hi:a∈MulAut.innerSubgroup (BinaryCarrier n hn))
    (f:K→*a.fixedSubgroup) (hf:Function.Injective f) (S:Sylow 2 K) :
    IsMulCommutative S := by
  obtain ⟨x,hx⟩:=hi
  have ho:orderOf x=2:=
    (MulAut.conj_orderOf_of_center_eq_bot (binaryCarrier_center_eq_bot n hn) x).symm.trans
      ((congrArg orderOf hx).trans ha)
  change MulAut.conj x=a at hx
  have hR:zpowers x≠⊥:=by
    intro h
    have hx1:=zpowers_eq_bot.mp h
    simp [hx1] at ho
  have hp:IsPGroup 2 (zpowers x):=IsPGroup.of_card (n:=1)
    (by rw [Nat.card_zpowers,ho,pow_one])
  obtain ⟨g,b,hcover⟩:=TwoLocalCover.normalizer_cover n hn (zpowers x) hR hp
  have hCN:a.fixedSubgroup≤normalizer (zpowers x:Set (BinaryCarrier n hn)) := by
    rw [←hx,MulAut.fixedSubgroup_conj]
    rw [←centralizer_closure ({x}:Set (BinaryCarrier n hn)),←zpowers_eq_closure]
    exact centralizer_le_normalizer _
  let r:a.fixedSubgroup→*parabolic (binaryParameters n hn) b:=
    ((MulAut.conj g).toMonoidHom.comp a.fixedSubgroup.subtype).codRestrict _
      (fun y=>hcover (mem_map_of_mem _ (hCN y.property)))
  have hr:Function.Injective r:=by
    intro y z h
    exact Subtype.ext ((MulAut.conj g).injective (congrArg Subtype.val h))
  exact sylow_commutative_of_simple_parabolic_embedding (binaryParameters n hn) rfl b
    (r.comp f) (hr.comp hf) S
end Triality.Standard.InvolutionFixedComponents

namespace Triality.Standard.EvenField
open OuterOdd

/-- Every ordinary outer fixed component is the entire genuine smaller carrier. -/
theorem outer_fixed_component (n:ℕ) (hn:0<n)
    (a:MulAut (BinaryCarrier n hn)) (ha:orderOf a=2)
    (hout:a∉MulAut.innerSubgroup (BinaryCarrier n hn))
    (D:Subgroup a.fixedSubgroup) (hD:IsComponent a.fixedSubgroup D) :
    ∃(m:ℕ)(hm:0<m),n=2*m ∧
      ∃E:a.fixedSubgroup≃*BinaryCarrier m hm,
        D.map E.toMonoidHom=⊤ ∧ Nonempty (D≃*BinaryCarrier m hm) ∧ primeRank 2 D=5*m := by
  obtain ⟨m,hm,hnm,⟨E⟩⟩:=InvolutionTwoComponents.binary_outer_fixed_equiv n hn a ha hout
  let : IsSimpleGroup a.fixedSubgroup:=E.isSimpleGroup
  have htop:D=⊤ := by
    rcases hD.1.eq_bot_or_top_of_isSimpleGroup inferInstance with hb|ht
    · let : IsQuasisimple D:=hD.2
      let : IsSimpleGroup (D⧸center D):=IsQuasisimple.simple
      let : Nontrivial D:=(QuotientGroup.mk'_surjective (center D)).nontrivial
      exact ((nontrivial_iff_ne_bot D).mp inferInstance hb).elim
    · exact ht
  let d:D≃*BinaryCarrier m hm:=(MulEquiv.subgroupCongr htop).trans (Subgroup.topEquiv.trans E)
  refine ⟨m,hm,hnm,E,?_,⟨d⟩,?_⟩
  · rw [htop,←MonoidHom.range_eq_map,MonoidHom.range_eq_top.mpr E.surjective]
  · rw [primeRank_equiv 2 d]
    exact TwoRank.twoRank_eq_five_mul m hm

/-- An ordinary outer fixed component has two-rank greater than two. -/
theorem outer_fixed_component_rank_gt_two (n:ℕ) (hn:0<n)
    (a:MulAut (BinaryCarrier n hn)) (ha:orderOf a=2)
    (hout:a∉MulAut.innerSubgroup (BinaryCarrier n hn))
    (D:Subgroup a.fixedSubgroup) (hD:IsComponent a.fixedSubgroup D) :
    2<primeRank 2 D := by
  obtain ⟨m,hm,_,E,_,_,hr⟩:=outer_fixed_component n hn a ha hout D hD
  omega
/-- The same obstruction retains an arbitrary original carrier and its actual fixed component. -/
theorem outer_fixed_component_rank_gt_two_of_equiv {E:Type*} [Group E]
    (n:ℕ) (hn:0<n) (e:E≃*BinaryCarrier n hn)
    (a:MulAut E) (ha:orderOf a=2) (hout:∀g:E,a≠MulAut.conj g)
    (D:Subgroup a.fixedSubgroup) (hD:IsComponent a.fixedSubgroup D) :
    2<primeRank 2 D := by
  let : Finite E:=Finite.of_injective e e.injective
  have hao:orderOf (MulAut.congr e a)=2:=((MulAut.congr e).orderOf_eq a).trans ha
  have hout':MulAut.congr e a∉MulAut.innerSubgroup (BinaryCarrier n hn) := by
    rintro ⟨g,hg⟩
    obtain ⟨d,hd⟩:=(MulAut.congr_inner_iff e a).mp ⟨g,hg.symm⟩
    exact hout d hd
  let ef:=MulAut.fixedSubgroupCongr e a
  have hr:=outer_fixed_component_rank_gt_two n hn (MulAut.congr e a) hao hout'
    (D.map ef.toMonoidHom) (hD.map_equiv ef)
  let eD:D≃*D.map ef.toMonoidHom:=ef.subgroupMap D
  rw [primeRank_equiv 2 eD]
  exact hr

end Triality.Standard.EvenField

