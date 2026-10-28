module
public import Stellmacher.SectionTen.TenOneSmallResidualCentralDisplacement
public import Stellmacher.SectionTen.TenOneSmallPrimitiveCentralizer

/-!
# A primitive point in the two small residual cores

For the actual order-eight first-module and SL₂(2) quotient case, the first
and middle residual two-cores contain a common element with nontrivial square.
The middle is the literal offset-two vertex. No centralizer cardinality or
extra commutator hypothesis is assumed.

The middle residual is C₄×C₄ and its square-one subgroup is exactly the middle
central plane. If their common intersection contained only involutions, mutual
normalization would put the residual commutator in this plane; the proved
square-preserving refinement puts it in the first central line. The subgroup
Rfirst∩Qmiddle has order at least sixteen because the edge/core index is two.
Each of its elements acts on the abelian middle residual with displacement
image of order at most two, so its fixed subgroup has order at least eight.
It therefore fixes a primitive point. The actual primitive-point centralizer
then puts that element in the middle residual, forcing the whole order-sixteen
subgroup into the middle central plane of order four, a contradiction.

This supplies the implicit primitive intersection needed for the Wstar
centralizer equality before Stellmacher (10.1)(a3)(8), Journal of Algebra
190 (1997), printed p.61. Both residual cores, the chosen point, and every
conjugation action remain in the original ambient context.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
open scoped commutatorElement IsMulCommutative
universe u

set_option maxHeartbeats 1200000 in
public theorem ten_one_small_residual_intersection_primitive
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep)=8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    ∃ x:G, x∈twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep) ∧
      x∈twoCoreIn (EAt ctx.Γ middle) ∧ x^2≠1 := by
  classical
  let Γ := ctx.Γ
  let first := ctx.criticalPath.firstStep
  let R := twoCoreIn (EAt Γ first)
  let D := twoCoreIn (EAt Γ middle)
  let Z := ZAt Γ middle
  let Zfirst := ZAt Γ first
  let Q := QAt Γ middle
  have hcore (v:Γ.Vertex) : twoCoreIn (EAt Γ v)≤QAt Γ v := by
    change twoCoreIn (Γ.twoResidualAt v)≤Γ.twoCoreAt v
    rw [Γ.twoResidualAt_def,Γ.twoCoreAt_def,residual_core_eq_inter_core]
    exact inf_le_right
  have hQlocal (v:Γ.Vertex) : QAt Γ v≤GAt Γ v := by
    rw [QAt,q,Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hnormal (v:Γ.Vertex) : GAt Γ v≤Subgroup.normalizer (twoCoreIn (EAt Γ v):Set G) := by
    have hE : EAt Γ v=twoResidualIn (GAt Γ v) := Γ.twoResidualAt_def v
    have hEP : EAt Γ v≤GAt Γ v := hE ▸ twoResidualIn_le _
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer ((twoCoreIn_le _).trans hEP)).mp
      (twoCoreIn_normal_of_normal _ _ hEP (hE ▸ twoResidualIn_normal _))
  obtain ⟨_,hadj,_,_⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hQfirst : Q≤GAt Γ first :=
    ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core middle first
      ((mem_neighborhood_iff_adjacent Γ).mpr hadj) default).2.2
  have hRmiddle : R≤GAt Γ middle := (hcore first).trans
    ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core first middle
      ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hadj)) default).2.2
  have hDfirst : D≤GAt Γ first := (hcore middle).trans hQfirst
  have hRD : R≤Subgroup.normalizer (D:Set G) := hRmiddle.trans (hnormal middle)
  have hDR : D≤Subgroup.normalizer (R:Set G) := hDfirst.trans (hnormal first)
  have hZD : Z≤D := ten_one_middle_center_le_residual_core ctx middle hpath
  have hZcard : Nat.card Z=4 := (sectionTenOpeningData ctx middle hpath).center_card
  have hZfirstCard : Nat.card Zfirst=2 :=
    (nine_next_center_commutator_and_kernel ctx.toAmbientSectionNineContext
      (by rw [ctx.critical_length]; decide) first ⟨1,Γ.act_one _⟩).1
  have hZfirstZ : Zfirst≤Z := by
    rw [show Z=ZAt Γ first⊔ZAt Γ ctx.criticalPath.a' from
      (sectionTenOpeningData ctx middle hpath).center_direct_product.1]
    exact le_sup_left
  have hZfirstD : Zfirst≤D := hZfirstZ.trans hZD
  obtain ⟨equiv⟩ := ten_one_middle_residual_c4_square ctx middle hpath hsmall hmodel
  let _ : CommGroup D := equiv.toMonoidHom.commGroupOfInjective equiv.injective
  have hDcard : Nat.card D=16 := by
    rw [Nat.card_congr equiv.toEquiv]
    norm_num [Nat.card_prod,Nat.card_eq_fintype_card]
  let _ : IsElementaryAbelian 2 Z := by
    rw [show Z=omegaOneCenter Q from (sectionTenOpeningData ctx middle hpath).center_omega]
    exact omegaOneCenterAmbient_elementaryAbelian _
  let squares : D→*D := powMonoidHom 2
  have hZker : Z.subgroupOf D≤squares.ker := by
    intro z hz
    apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian (p:=2) (A:=Z) z hz
  have hkerCard : Nat.card squares.ker≤4 := by
    let f : squares.ker→{v:C4×C4 // v^2=1} := fun x =>
      ⟨equiv x,by rw [←map_pow]; exact (congrArg equiv x.property).trans equiv.map_one⟩
    have hf : Function.Injective f := by
      intro x y heq
      exact Subtype.ext (equiv.injective (congrArg Subtype.val heq))
    have hc : Nat.card {v:C4×C4 // v^2=1}=4 := by
      rw [Nat.card_eq_fintype_card]
      decide
    exact hc ▸ Nat.card_le_card_of_injective f hf
  have hZkerEq : Z.subgroupOf D=squares.ker := Subgroup.eq_of_le_of_card_ge hZker (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZD).toEquiv,hZcard]
    exact hkerCard)
  have hinvol (d:D) (hd:d^2=1) : (d:G)∈Z := by
    have hh : d∈squares.ker := hd
    rwa [←hZkerEq] at hh
  by_contra! hnone
  have hIZ : R⊓D≤Z := by
    intro x hx
    exact hinvol ⟨x,hx.2⟩ (Subtype.ext (hnone x hx.1 hx.2))
  have hcomm : ⁅D,R⁆≤Zfirst := by
    apply ten_one_small_residual_commutator_le_first_center ctx middle hpath hsmall hmodel D hDfirst
    exact (le_inf (Subgroup.le_normalizer_iff_commutator_le_right.mp hDR)
      (Subgroup.le_normalizer_iff_commutator_le_left.mp hRD)).trans hIZ
  let P := R⊓Q
  have hRcard : Nat.card R=32 := ten_one_small_residual_core_card ctx middle hpath hsmall hmodel
  let edge := GAt Γ middle⊓GAt Γ first
  have hQedge : Q≤edge := le_inf (hQlocal middle) hQfirst
  have hRedge : R≤edge := le_inf hRmiddle ((hcore first).trans (hQlocal first))
  have hedgeCard : Nat.card edge=2*Nat.card Q :=
    (cubic_local_action_of_sl2Two_quotient Γ ctx.sectionSeven middle
      (sectionTenOpeningData ctx middle hpath).quotient_model).edge_card first hadj
  have hindex : Q.relIndex edge=2 := by
    have hh := (Q.subgroupOf edge).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQedge).toEquiv] at hh
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (hh.trans hedgeCard)
  have hPindex : P.relIndex R≤2 := by
    change (R⊓Q).relIndex R≤2
    rw [Subgroup.inf_relIndex_left]
    have hh := Subgroup.relIndex_le_of_le_right (H:=Q) hRedge
      (show Q.relIndex edge≠0 from (Q.subgroupOf edge).index_ne_zero_of_finite)
    rwa [hindex] at hh
  have hPlarge : 16≤Nat.card P := by
    have hh := (P.subgroupOf R).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show P≤R from inf_le_left)).toEquiv,hRcard] at hh
    change P.relIndex R*Nat.card P=32 at hh
    nlinarith only [hh,hPindex,Nat.zero_le (Nat.card P)]
  have hPD : P≤D := by
    intro p hp
    let action : MulAut D := D.normalizerMonoidHom ⟨p,hRD hp.1⟩
    let delta : D→*D := {
      toFun d := d⁻¹*action d
      map_one' := by simp
      map_mul' := by intro a b; simp only [map_mul,mul_inv_rev]; ac_rfl }
    have hdelta : delta.range≤Zfirst.subgroupOf D := by
      rintro d ⟨v,rfl⟩
      change (v:G)⁻¹*(p*(v:G)*p⁻¹)∈Zfirst
      have hh := hcomm (Subgroup.commutator_mem_commutator (D.inv_mem v.property) hp.1)
      simpa only [commutatorElement_def,inv_inv,mul_assoc] using hh
    have hsmallImage : Nat.card delta.range≤2 := by
      have hh := Subgroup.card_le_of_le hdelta
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZfirstD).toEquiv,hZfirstCard] at hh
      exact hh
    have hfixedLarge : 8≤Nat.card delta.ker := by
      have hh := delta.ker.card_mul_index
      rw [Subgroup.index_ker,hDcard] at hh
      nlinarith only [hh,hsmallImage,Nat.zero_le (Nat.card delta.ker)]
    obtain ⟨fixed,hfixed,hprimitive⟩ : ∃ d:D, d∈delta.ker ∧ d^2≠1 := by
      by_contra! hno
      have hle : delta.ker≤Z.subgroupOf D := by intro d hd; exact hinvol d (hno d hd)
      have hh := Subgroup.card_le_of_le hle
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZD).toEquiv,hZcard] at hh
      omega
    have hfix : action fixed=fixed := (inv_mul_eq_one.mp hfixed).symm
    have hcommute : (fixed:G)*p=p*(fixed:G) := by
      have hh := congrArg Subtype.val hfix
      change p*(fixed:G)*p⁻¹=(fixed:G) at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    have hprimitiveG : (fixed:G)^2≠1 := by
      intro hh
      exact hprimitive (Subtype.ext hh)
    have hc := ten_one_small_primitive_middle_centralizer ctx middle hpath hsmall hmodel
      (fixed:G) fixed.property hprimitiveG
    apply hc.le
    refine ⟨hp.2,?_⟩
    change p∈Subgroup.centralizer ({(fixed:G)}:Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have heq : x=(fixed:G) := Set.mem_singleton_iff.mp hx
    exact heq.symm ▸ hcommute
  have hPZ : P≤Z := (le_inf inf_le_left hPD).trans hIZ
  have hbound := Subgroup.card_le_of_le hPZ
  rw [hZcard] at hbound
  omega

end Stellmacher.SectionTen
