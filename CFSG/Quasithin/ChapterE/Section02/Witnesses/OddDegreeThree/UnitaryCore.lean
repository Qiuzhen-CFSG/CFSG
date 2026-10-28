module
public import Theory.SpecificGroups.SU3.OddInvolutionFixed.NoSL2
public import CFSG.Quasithin.ChapterE.Section02.Structure.OddDegreeThree.Unitary
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.CentralizerStructure.FourAction
import all CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.CentralizerStructure.FourAction
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport
public import Theory.GroupTheory.SolvableOuterQuotient
/-!
# The normal odd unitary source exclusion

E.2.2 forces p≡1 mod4, hence p>3, and identifies the actual maximal Sylow
overgroup M with an inner-involution centralizer. Its solvable residual is
SL₂(p), a normal component, and therefore centralizes O₂(M). An outer
involution cannot centralize this component: its actual fixed group is
SO₃(p), which admits no injection from SL₂(p). Thus every elementary
subgroup of O₂(M) lies in the original simple unitary component K.

A noncyclic elementary subgroup of K has abelian centralizer, contradicting
the same perfect SL₂(p) subgroup. Consequently its order is at most two.
The image theorem uses the caller's literal quotient map and the marking
of M; no TI descent, model-output hypothesis, or additional representation
is introduced. The internal FourAction import reuses its proved quasisimple
SL₂ transport inside this source family.

Source: Aschbacher–Smith E.2.2(2d) and E.2.7, pp.215–219; the full
involution-centralizer residual is the earlier E.1.14 geometry.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Structure.OddDegreeThree
open ValuesOdd.PSUThreeGeneration BenderSuzuki.MatrixGroups
open Chapter1.XiEmbedding.InvariantLarge.OddCartan.UnitaryPosition
variable {H:Type*} [Group H] [Finite H]

omit [Finite H] in
private theorem outer_fixed_no_sl2 [IsSimpleGroup H]
    {p:ℕ} (hp:p.Prime) (ho:Odd p) (hlarge:3<p) (hm:ClassicalGroup.IsPSU H 3 p)
    (a:MulAut H) (ha:a^2=1) (houter:¬∃k,a=MulAut.conj k)
    (f:Matrix.SpecialLinearGroup (Fin 2) (ZMod p)→*a.fixedSubgroup) : ¬Function.Injective f := by
  obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩:=hm
  let : Fact p.Prime:=⟨hp⟩
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J):=e.symm.isSimpleGroup
  have hfixed:Nat.card {x:F // J.conj x=x}=p := by
    simpa only [pow_one] using FiniteField.card_fixed_of_quadratic_frobenius J.conj p 1
      (by decide) (by simpa only [pow_one] using hF) (by simpa only [pow_one] using hconj)
  let b:=MulAut.congr e a
  have hb:b^2=1 := by rw [←map_pow,ha,map_one]
  have hbouter:¬∃k,b=MulAut.conj k := by
    intro h
    exact houter ((MulAut.congr_inner_iff e a).mp h)
  let c:=MulAut.fixedSubgroupCongr e a
  exact fun hf=>HermitianForm.OddInvolutionNormalization.no_sl2_in_outer_fixed J
    hp ho hlarge hF hfixed b hb hbouter (c.toMonoidHom.comp f) (c.injective.comp hf)

/-- The actual two-core of the unitary source overgroup has no elementary
subgroup of order four. This needs no TI hypothesis. -/
theorem unitary_elementary_card_le_two
    (T:Sylow 2 H) (hP:ChapterB.IsMinimalParabolicOver T ⊤)
    (K:Subgroup H) [K.Normal] [IsSimpleGroup K]
    (hgen:K⊔(T:Subgroup H)=⊤) (hcore:pCore 2 H=⊥)
    {p:ℕ} (hp:p.Prime) (ho:Odd p) (hm:ClassicalGroup.IsPSU K 3 p)
    (V:Subgroup H) [IsElementaryAbelian 2 V]
    (hVcore:V≤(ChapterB.minimalParabolicMax T hP).pCoreIn 2) : Nat.card V≤2 := by
  let : Fact p.Prime:=⟨hp⟩
  obtain ⟨hmod,t,ht,_,_,hM,_⟩:=unitary_centralizer_congruence T hP K hgen hp ho hm
  have hlarge:3<p := by have := hp.two_le; omega
  let C:=centralizer ({(t:H)}:Set H)
  have hVC:V≤C.pCoreIn 2 := by
    change V≤(centralizer ({(t:H)}:Set H)).pCoreIn 2
    simpa only [hM] using hVcore
  obtain ⟨e⟩:=inner_centralizer_residual_equiv K T hgen hp ho hlarge hm (t:H) t.property
    ((orderOf_injective K.subtype K.subtype_injective t).trans ht)
  let R:=solvableResidual C
  let : IsQuasisimple R:=quasisimple_of_sl2_equiv hlarge e
  let : IsSimpleGroup (R ⧸ center R):=IsQuasisimple.simple
  let : Nontrivial R:=(QuotientGroup.mk'_surjective (center R)).nontrivial
  have hcomp:IsComponent C R:=⟨(inferInstance:R.Normal).isSubnormal,inferInstance⟩
  have hcomm:⁅R,pCore 2 C⁆=⊥ := by
    rcases hcomp.normal_dichotomy (pCore 2 C) with hl|hc
    · let : Group.IsNilpotent (pCore 2 C):=pCore_isPGroup.isNilpotent
      let : Group.IsSolvable R:=Group.isSolvable_of_isSolvable_injective (inclusion_injective hl)
      exact (Group.IsPerfect.not_isSolvable R inferInstance).elim
    · exact hc
  let D:=R.map C.subtype
  have hDV:D≤centralizer (V:Set H) := by
    rintro d ⟨x,hx,rfl⟩ v hv
    obtain ⟨y,hy,rfl⟩:=hVC hv
    exact congrArg Subtype.val ((commutator_eq_bot_iff_le_centralizer.mp hcomm) hx y hy)
  have hQ:=isPGroup_quotient_of_sup_eq_top K T T.isPGroup' hgen
  let : Group.IsNilpotent (H ⧸ K):=hQ.isNilpotent
  let : Group.IsPerfect D:=Group.IsPerfect.map C.subtype
  have hDK:D≤K:=le_of_isPerfect_of_solvable_quotient D K
  let j:R→*K :=
    { toFun x:=⟨x.val.val,hDK (mem_map_of_mem C.subtype x.property)⟩
      map_one':=rfl
      map_mul' _ _:=rfl }
  have hj:Function.Injective j := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun k:K=>(k:H)) h))
  let : Group.IsPerfect K:=isPerfect_of_model hp ho hm
  have hcent:centralizer (K:Set H)=⊥ := centralizer_eq_bot_of_simple_two_quotient K
    (Group.IsPerfect.not_isMulCommutative K) hQ hcore
  have hVK:V≤K := by
    intro v hv
    let a:MulAut K:=MulAut.conjNormal v
    have ha:a^2=1 := by
      change (MulAut.conjNormal (H:=K):H→*MulAut K) v^2=1
      rw [←map_pow,elemPow_eq_one_of_isElementaryAbelian (p:=2) v hv,map_one]
    by_contra hvK
    have houter:¬∃k,a=MulAut.conj k := by
      rintro ⟨k,hk⟩
      have hi:=MulAut.conjNormal_injective_of_centralizer_eq_bot K hcent
      have heq:(MulAut.conjNormal (H:=K) (k:H))=MulAut.conj k := by ext x; rfl
      have he:v=(k:H) := hi (by rw [heq]; exact hk)
      exact hvK (he ▸ k.property)
    let jf:R→*a.fixedSubgroup :=
      { toFun x:=⟨j x,by
          rw [MulAut.mem_fixedSubgroup]
          apply Subtype.ext
          change v*x.val.val*v⁻¹=x.val.val
          have hc:=hDV (mem_map_of_mem C.subtype x.property) v hv
          change v*x.val.val=x.val.val*v at hc
          rw [hc,mul_inv_cancel_right]⟩
        map_one':=Subtype.ext j.map_one
        map_mul' x y:=Subtype.ext (j.map_mul x y) }
    have hjf:Function.Injective jf:=fun x y h=>hj (congrArg Subtype.val h)
    exact outer_fixed_no_sl2 hp ho hlarge hm a ha houter (jf.comp e.symm.toMonoidHom)
      (hjf.comp e.symm.injective)
  let W:=V.subgroupOf K
  let : IsElementaryAbelian 2 W:=IsElementaryAbelian.subgroupOf hVK
  have hcyc:IsCyclic W := by
    by_contra hn
    have hc:IsMulCommutative (centralizer (W:Set K)) :=
      (isPSU_centralizer_bound_of_matrix_centralizers (p:=2) (q:=p) (by decide)
        (by intro h; subst p; norm_num at ho) hm W (IsElementaryAbelian.isPGroup 2 W) hn
        (by intro F _ _ B hcomm horder hnB hdet
            let : IsMulCommutative B:=hcomm
            exact Representation.rankThreeDeterminantCentralizer B horder hnB hdet)).1
    let : IsMulCommutative (centralizer (W:Set K)):=hc
    let k:R→*centralizer (W:Set K):=
      { toFun x:=⟨j x,by
          intro w hw
          exact Subtype.ext (hDV (mem_map_of_mem C.subtype x.property) w hw)⟩
        map_one':=Subtype.ext j.map_one
        map_mul' x y:=Subtype.ext (j.map_mul x y) }
    have hk:Function.Injective k:=fun x y h=>hj (congrArg Subtype.val h)
    let : Group.IsSolvable (centralizer (W:Set K)):=Group.isSolvable_of_comm (isMulCommutative_iff.mp hc)
    let : Group.IsSolvable R:=Group.isSolvable_of_isSolvable_injective hk
    exact Group.IsPerfect.not_isSolvable R inferInstance
  have hc:Nat.card W∣2 := by
    rw [←hcyc.exponent_eq_card]
    exact IsElementaryAbelian.exponent_dvd_p 2 W
  rw [←Nat.card_congr (subgroupOfEquivOfLe hVK).toEquiv]
  exact Nat.le_of_dvd (by decide) hc
omit [Finite H] in
private theorem map_pCoreIn_le {Q:Type*} [Group Q] (f:H→*Q) (M:Subgroup H) :
    (M.pCoreIn 2).map f≤(M.map f).pCoreIn 2 := by
  let g:=f.subgroupMap M
  have hc:(pCore 2 M).map g≤pCore 2 (M.map f) :=
    le_sSup ⟨Subgroup.Normal.map inferInstance g (f.subgroupMap_surjective M),pCore_isPGroup.map g⟩
  have hh:=map_mono (f:=(M.map f).subtype) hc
  have he:(M.map f).subtype.comp g=f.comp M.subtype := by ext x; rfl
  simpa only [pCoreIn,map_map,he] using hh

omit [Finite H] in
/-- The unitary source bound through the original quotient map. -/
theorem unitary_image_card_le_two
    (M V:Subgroup H) [IsElementaryAbelian 2 V] (hVcore:V≤M.pCoreIn 2)
    {Q:Type*} [Group Q] [Finite Q] (f:H→*Q)
    (Tq:Sylow 2 Q) (hPq:ChapterB.IsMinimalParabolicOver Tq ⊤)
    (K:Subgroup Q) [K.Normal] [IsSimpleGroup K]
    (hgen:K⊔(Tq:Subgroup Q)=⊤) (hcore:pCore 2 Q=⊥)
    {p:ℕ} (hp:p.Prime) (ho:Odd p) (hm:ClassicalGroup.IsPSU K 3 p)
    (hM:M.map f=ChapterB.minimalParabolicMax Tq hPq) :
    Nat.card (V.map f)≤2 := by
  let : IsElementaryAbelian 2 (V.map f):=IsElementaryAbelian.map f
  apply unitary_elementary_card_le_two Tq hPq K hgen hcore hp ho hm (V.map f)
  rw [←hM]
  exact (map_mono hVcore).trans (map_pCoreIn_le f M)
end CFSG.Quasithin.ChapterE.Structure.OddDegreeThree
