module

public import Theory.GroupTheory.CubicExtraspecialMaxAbelian
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicLine.FixedSection

/-!
# The original unique maximum abelian subgroup in the ternary Sylow product

The original elementary kernel V has order81. The preceding moved-line
normalizer argument makes D extraspecial of order243. On the same independent
cubic axes used for its complement, the source fixedspace theorem supplies
the outside-centralizer implication. Ternary pairing and product counts then
show that every abelian subgroup escaping V has order at most27.

The surviving inputs are precisely the earlier moved-line placement and
normalizer-index24 hypotheses, owned by the line-normalizer source theorem.
Neither a fixedspace nor a maximum-abelian conclusion is assumed.
Source: Aschbacher, Sporadic Groups (1994),45.8(2),last paragraph,p246.
-/

public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
variable {G:Type*} [Group G] [Finite G] {z:G} (h:IsType z)
include h in
theorem cubic_line_marked_maximum_abelian (P:Sylow 3 (centralizer z))
    (actors:QuaternionIndependentCubics h.toCentralizerHypothesis.factorData.leftCore
      h.toCentralizerHypothesis.factorData.rightCore)
    (ha:actors.A=(P:Subgroup (centralizer z)).map (centralizer z).subtype)
    (hsplit:normalizer (zpowers (actors.x:G):Set G)=CubicLine.oddKernel (zpowers (actors.x:G))⊔
      (normalizer (zpowers (actors.x:G):Set G)⊓centralizer z))
    (hD:Nat.card (CubicLine.oddKernel (zpowers (actors.x:G)))=243)
    (he:IsExtraspecial 3 (CubicLine.oddKernel (zpowers (actors.x:G)))) :
    let V:=CubicNormalizer.oddKernel ((P:Subgroup (centralizer z)).map (centralizer z).subtype)
    let D:=CubicLine.oddKernel (zpowers (actors.x:G))
    ∀B:Subgroup G,IsMulCommutative B→B≤V⊔D→
      (¬B≤V→Nat.card B≤27) ∧ (81≤Nat.card B→B=V) := by
  let X:=(P:Subgroup (centralizer z)).map (centralizer z).subtype
  let V:=CubicNormalizer.oddKernel X
  let W:=zpowers (actors.x:G)
  let D:=CubicLine.oddKernel W
  let d:=h.toCentralizerHypothesis.factorData
  have hB:Nonempty (d.leftCore≃*QuaternionGroup 2):=⟨Factors.factorCoreEquiv d.left d.left_model.some⟩
  have hi:Nat.card (d.leftCore⊓d.rightCore:Subgroup G)=2:=by
    rw [d.core_intersection h.involution,Nat.card_zpowers,h.involution]
  have hc:∀b∈d.leftCore,∀c∈d.rightCore,b*c=c*b:=fun b hb c hc=>
    d.factors_commute h.involution b (pCoreIn_le 2 d.left hb) c (pCoreIn_le 2 d.right hc)
  have hfixed:Nonempty ((core z⊓Subgroup.centralizer (W:Set G):Subgroup G)≃*QuaternionGroup 2):=by
    rw [←d.core_span h.involution,actors.fixed_core_left hB hi hc]
    exact ⟨Factors.factorCoreEquiv d.right d.right_model.some⟩
  have hWX:W≤X:=zpowers_le.mpr (ha.le actors.x.property)
  have hW:Nat.card W=3:=by rw [Nat.card_zpowers,actors.x_order]
  obtain ⟨hV,hVc⟩:=h.original_cubic_kernel_eighty_one P
  let :IsElementaryAbelian 3 V:=hV
  let :IsExtraspecial 3 D:=he
  have hI:Nat.card (V⊓D:Subgroup G)=27:=
    (h.cubic_line_kernel_intersection X W (h.cubic_sylow_image_card P) (map_subtype_le _)
      hW hWX hfixed hsplit hV hVc).2
  have hVD:V≤normalizer (D:Set G):=
    (((map_subtype_le _:V≤Subgroup.centralizer (X:Set G)).trans (centralizer_le hWX)).trans
      (centralizer_le_normalizer _)).trans (CubicLine.normalizer_normalizes_oddKernel W)
  have hf:=h.cubic_line_marked_outside_fixed P actors ha hsplit hD
  change ∀B:Subgroup G, IsMulCommutative B → B≤V⊔D →
    (¬B≤V→Nat.card B≤27) ∧ (81≤Nat.card B→B=V)
  intro B hB hBP
  let :IsMulCommutative B:=hB
  exact ⟨cubic_extraspecial_abelian_card_le V D hVc hD hI hVD hf B hBP,
    cubic_extraspecial_unique_maximum_abelian V D hVc hD hI hVD hf B hBP⟩

include h in
theorem cubic_line_maximum_abelian_of_moved_line (P:Sylow 3 (centralizer z))
    (actors:QuaternionIndependentCubics h.toCentralizerHypothesis.factorData.leftCore
      h.toCentralizerHypothesis.factorData.rightCore)
    (ha:actors.A=(P:Subgroup (centralizer z)).map (centralizer z).subtype)
    (F:Subgroup G)
    (hsplit:normalizer (zpowers (actors.x:G):Set G)=CubicLine.oddKernel (zpowers (actors.x:G))⊔
      (normalizer (zpowers (actors.x:G):Set G)⊓centralizer z))
    (hS:∃S:Sylow 2 (normalizer (zpowers (actors.x:G):Set G)),Nonempty (S≃*QuaternionGroup 4))
    (hF:Nat.card F=3)
    (hFV:F≤CubicNormalizer.oddKernel ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (hFD:F≤CubicLine.oddKernel (zpowers (actors.x:G)))
    (hVN:normalizer (F:Set G)≤normalizer
      (CubicNormalizer.oddKernel ((P:Subgroup (centralizer z)).map (centralizer z).subtype):Set G))
    (hindex:(CubicNormalizer.oddKernel ((P:Subgroup (centralizer z)).map (centralizer z).subtype)).relIndex
      (normalizer (F:Set G))=24) :
    let V:=CubicNormalizer.oddKernel ((P:Subgroup (centralizer z)).map (centralizer z).subtype)
    let D:=CubicLine.oddKernel (zpowers (actors.x:G))
    ∀B:Subgroup G,IsMulCommutative B→B≤V⊔D→
      (¬B≤V→Nat.card B≤27) ∧ (81≤Nat.card B→B=V) := by
  let d:=h.toCentralizerHypothesis.factorData
  have hB:Nonempty (d.leftCore≃*QuaternionGroup 2):=⟨Factors.factorCoreEquiv d.left d.left_model.some⟩
  have hi:Nat.card (d.leftCore⊓d.rightCore:Subgroup G)=2:=by
    rw [d.core_intersection h.involution,Nat.card_zpowers,h.involution]
  have hc:∀b∈d.leftCore,∀c∈d.rightCore,b*c=c*b:=fun b hb c hc=>
    d.factors_commute h.involution b (pCoreIn_le 2 d.left hb) c (pCoreIn_le 2 d.right hc)
  have hfixed:Nonempty ((core z⊓Subgroup.centralizer (zpowers (actors.x:G):Set G):Subgroup G)≃*QuaternionGroup 2):=by
    rw [←d.core_span h.involution,actors.fixed_core_left hB hi hc]
    exact ⟨Factors.factorCoreEquiv d.right d.right_model.some⟩
  have hW:Nat.card (zpowers (actors.x:G))=3:=by rw [Nat.card_zpowers,actors.x_order]
  have hWX:zpowers (actors.x:G)≤(P:Subgroup (centralizer z)).map (centralizer z).subtype:=
    zpowers_le.mpr (ha.le actors.x.property)
  obtain ⟨_,hD,_,he,_⟩:=h.original_cubic_line_fitting_of_moved_line P _ F hW hWX hfixed
    hsplit hS hF hFV hFD hVN hindex
  exact h.cubic_line_marked_maximum_abelian P actors ha hsplit hD he
end Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
