module

public import Theory.GroupTheory.QuaternionCubicSylowCensus
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicLine.Complement.Canonical
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicLine.OriginalKernel

/-!
# The original cubic Sylow census and stabilizer of order thirty-six

The original complement K has a normal SL₂(3) subgroup of index two, so
there are exactly four cubic Sylow subgroups. The canonical quotient by
D=O₂′(N_G(W)), once the earlier source supplies |D|=243, transfers this
census to N_G(W). Its Sylow normalizer has order2916 and relative index36
over the original elementary kernel V of order81.

The marked producer retains the supplied reflections and chooses the cubic
axes once through their actual complement construction. The original wrapper
constructs the reflected marking. Only the independently proved order243
clause remains explicit; no complement or model conclusion is assumed there.
The separate global-normalizer identification belongs to the source assembly.
Source: Aschbacher, Sporadic Groups (1994),45.9,printed pp246–247.
-/

public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
variable {G:Type*} [Group G] [Finite G] {z:G} (h:IsType z)
include h in
theorem cubic_line_normalizer_census_of_complement (P:Sylow 3 (centralizer z)) (W K:Subgroup G)
    (hW:Nat.card W=3) (hWX:W≤(P:Subgroup (centralizer z)).map (centralizer z).subtype)
    (hfixed:Nonempty ((core z⊓Subgroup.centralizer (W:Set G):Subgroup G)≃*QuaternionGroup 2))
    (hsplit:normalizer (W:Set G)=CubicLine.oddKernel W⊔(normalizer (W:Set G)⊓centralizer z))
    (hK:Nat.card K=48) (hKN:K≤normalizer (W:Set G))
    (hgen:normalizer (W:Set G)=CubicLine.oddKernel W⊔K)
    (hdis:Disjoint (CubicLine.oddKernel W) K) (hcount:Nat.card (Sylow 3 K)=4)
    (hD:Nat.card (CubicLine.oddKernel W)=243) :
    let V:=CubicNormalizer.oddKernel ((P:Subgroup (centralizer z)).map (centralizer z).subtype)
    let Q:=V⊔CubicLine.oddKernel W
    Nat.card (normalizer (Q:Set G)⊓normalizer (W:Set G):Subgroup G)=2916 ∧
      V.relIndex (normalizer (Q:Set G)⊓normalizer (W:Set G))=36 := by
  let X:=(P:Subgroup (centralizer z)).map (centralizer z).subtype
  let V:=CubicNormalizer.oddKernel X
  let D:=CubicLine.oddKernel W
  let M:=normalizer (W:Set G)
  let Q:=V⊔D
  have hX:=h.cubic_sylow_image_card P
  have hXH:X≤centralizer z:=map_subtype_le _
  obtain ⟨hV,hVc⟩:=h.original_cubic_kernel_eighty_one P
  have hVW:V≤Subgroup.centralizer (W:Set G):=(map_subtype_le _).trans (centralizer_le hWX)
  have hVM:V≤M:=hVW.trans (centralizer_le_normalizer _)
  have hDM:D≤M:=map_subtype_le _
  have hQM:Q≤M:=sup_le hVM hDM
  have hVD:V≤normalizer (D:Set G):=hVM.trans (CubicLine.normalizer_normalizes_oddKernel W)
  have hcap:Nat.card (V⊓D:Subgroup G)=27:=
    (h.cubic_line_kernel_intersection X W hX hXH hW hWX hfixed hsplit hV hVc).2
  have hQ:Nat.card Q=729:=by
    have hh:=card_mul_eq_card_inf_mul_card_sup_of_normalizes D V hVD
    rw [inf_comm,sup_comm,hD,hVc,hcap] at hh
    change 243*81=27*Nat.card Q at hh
    omega
  have hM:Nat.card M=11664:=by
    change Nat.card (normalizer (W:Set G))=11664
    rw [hgen,card_sup_eq_mul_of_normalizes_of_disjoint D K
      (hKN.trans (CubicLine.normalizer_normalizes_oddKernel W)) hdis,hD,hK]
  have hD':Nat.card (pPrimeCore 2 M)=243:=by
    change Nat.card ((pPrimeCore 2 M).map M.subtype)=243 at hD
    rwa [card_map_of_injective M.subtype_injective] at hD
  have hK':Nat.card (K.subgroupOf M)=48:=
    (Nat.card_congr (subgroupOfEquivOfLe hKN).toEquiv).trans hK
  have hcount':Nat.card (Sylow 3 (K.subgroupOf M))=4:=by
    rw [Sylow.card_eq_of_mulEquiv (subgroupOfEquivOfLe hKN),hcount]
  have hc:=CubicLine.oddCore_isComplement_of_factorization W K hKN hdis hgen
  have hQc:Nat.card (Q.subgroupOf M)=729:=
    (Nat.card_congr (subgroupOfEquivOfLe hQM).toEquiv).trans hQ
  have hf:Nat.factorization 11664 3=6:=by
    rw [Nat.factorization_def 11664 Nat.prime_three,show (11664:ℕ)=3^6*16 by norm_num,
      padicValNat_base_pow_mul (by norm_num) (by norm_num) 6,
      show padicValNat 3 16=0 from padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr (by norm_num)))]
  let S:Sylow 3 M:=Sylow.ofCard (Q.subgroupOf M) (by rw [hQc,hM,hf];decide)
  have hn:Nat.card (normalizer (Q.subgroupOf M:Set M))=2916:=
    cubic_sylow_normalizer_card_of_split (pPrimeCore 2 M) (K.subgroupOf M) hD' hK' hc hcount' S
  have hnG:Nat.card (normalizer (Q:Set G)⊓M:Subgroup G)=2916:=by
    rw [←subgroupOf_normalizer_eq hQM] at hn
    have hm:=card_map_of_injective (K:=(normalizer (Q:Set G)).subgroupOf M) (f:=M.subtype) M.subtype_injective
    rw [subgroupOf_map_subtype] at hm
    exact hm.trans hn
  have hVN:V≤normalizer (Q:Set G)⊓M:=le_inf
    ((show V≤Q from le_sup_left).trans Q.le_normalizer) hVM
  have hi:=relIndex_mul_relIndex (⊥:Subgroup G) V (normalizer (Q:Set G)⊓M) bot_le hVN
  rw [relIndex_bot_left,relIndex_bot_left,hVc,hnG] at hi
  change Nat.card (normalizer (Q:Set G)⊓M:Subgroup G)=2916 ∧ V.relIndex (normalizer (Q:Set G)⊓M)=36
  exact ⟨hnG,by omega⟩

include h in
theorem cubic_line_sylow_census (P:Sylow 3 (centralizer z))
    (m:CubicNormalizer.ReflectedMarking z ((P:Subgroup (centralizer z)).map (centralizer z).subtype)) :
    ∃actors:QuaternionIndependentCubics h.toCentralizerHypothesis.factorData.leftCore
      h.toCentralizerHypothesis.factorData.rightCore,
    actors.A=(P:Subgroup (centralizer z)).map (centralizer z).subtype ∧
    let W:=zpowers (actors.x:G)
    let J:=h.toCentralizerHypothesis.factorData.rightCore⊔zpowers (actors.y:G)
    let K:=J⊔zpowers (m.s*m.t)
    let V:=CubicNormalizer.oddKernel ((P:Subgroup (centralizer z)).map (centralizer z).subtype)
    let D:=CubicLine.oddKernel W
    Nat.card (Sylow 3 K)=4 ∧
    (Nat.card D=243 → Nat.card (normalizer ((V⊔D:Subgroup G):Set G)⊓normalizer (W:Set G):Subgroup G)=2916 ∧
      V.relIndex (normalizer ((V⊔D:Subgroup G):Set G)⊓normalizer (W:Set G))=36) := by
  obtain ⟨actors,ha,hW,hJ,hJc,hK,hKN,hWK,hl,hg,hd,hrJ,hfixed⟩:=h.cubic_line_complement_marked P m
  let J:=h.toCentralizerHypothesis.factorData.rightCore⊔zpowers (actors.y:G)
  let K:=J⊔zpowers (m.s*m.t)
  let W:=zpowers (actors.x:G)
  have hJK:J≤K:=le_sup_left
  let : (J.subgroupOf K).Normal:=normal_subgroupOf_of_le_normalizer
    (sup_le J.le_normalizer (zpowers_le.mpr hrJ))
  have hcJ:Nat.card (J.subgroupOf K)=24:=
    (Nat.card_congr (subgroupOfEquivOfLe hJK).toEquiv).trans hJc
  have he:(J.subgroupOf K)≃*Matrix.SpecialLinearGroup (Fin 2) (ZMod 3):=
    (subgroupOfEquivOfLe hJK).trans hJ.some
  have hcount:=cubic_sylow_count_of_sl2_three_index_two (J.subgroupOf K) hK hcJ he
  refine ⟨actors,ha,hcount,?_⟩
  intro hD
  have hWX:W≤(P:Subgroup (centralizer z)).map (centralizer z).subtype:=
    zpowers_le.mpr (ha.le actors.x.property)
  have hs:normalizer (W:Set G)=CubicLine.oddKernel W⊔(normalizer (W:Set G)⊓centralizer z):=by
    rw [inf_comm,hl,←sup_assoc,sup_eq_left.mpr (CubicLine.le_oddKernel W hW)]
    exact hg
  exact h.cubic_line_normalizer_census_of_complement P W K hW hWX hfixed hs hK
    (hKN.trans inf_le_right) hg hd hcount hD

include h in
theorem original_cubic_line_sylow_census (P:Sylow 3 (centralizer z)) :
    ∃m:CubicNormalizer.ReflectedMarking z ((P:Subgroup (centralizer z)).map (centralizer z).subtype),
    ∃actors:QuaternionIndependentCubics h.toCentralizerHypothesis.factorData.leftCore
      h.toCentralizerHypothesis.factorData.rightCore,
    actors.A=(P:Subgroup (centralizer z)).map (centralizer z).subtype ∧
    let W:=zpowers (actors.x:G)
    let J:=h.toCentralizerHypothesis.factorData.rightCore⊔zpowers (actors.y:G)
    let K:=J⊔zpowers (m.s*m.t)
    let V:=CubicNormalizer.oddKernel ((P:Subgroup (centralizer z)).map (centralizer z).subtype)
    let D:=CubicLine.oddKernel W
    Nat.card (Sylow 3 K)=4 ∧
    (Nat.card D=243 → Nat.card (normalizer ((V⊔D:Subgroup G):Set G)⊓normalizer (W:Set G):Subgroup G)=2916 ∧
      V.relIndex (normalizer ((V⊔D:Subgroup G):Set G)⊓normalizer (W:Set G))=36) := by
  obtain ⟨m⟩:=h.original_reflected_marking P
  exact ⟨m,h.cubic_line_sylow_census P m⟩
end Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
