module

public import Theory.GroupTheory.CubicExtraspecialFixedPlanes
public import Theory.GroupTheory.AbelianQuotientFixedSubgroup
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicLine.MaximumAbelian

/-!
# The original fixed planes for outside Sylow elements

Every outside element of the actual product V D fixes an order9 plane in V.
The product normalizes that plane and its central line W lies in it. The
proof uses the same original quaternion-cubic axes, the preceding fixedspace
calculation and extraspecial pairing; no action model or fixed-plane premise
is added to the original45.8 outputs.
Source: Aschbacher, Sporadic Groups (1994),45.9,printed p246.
-/

public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
variable {G:Type*} [Group G] [Finite G] {z:G} (h:IsType z)
include h in
theorem cubic_kernel_outside_fixed_planes (P:Sylow 3 (centralizer z))
    (actors:QuaternionIndependentCubics h.toCentralizerHypothesis.factorData.leftCore
      h.toCentralizerHypothesis.factorData.rightCore)
    (ha:actors.A=(P:Subgroup (centralizer z)).map (centralizer z).subtype)
    (hsplit:normalizer (zpowers (actors.x:G):Set G)=CubicLine.oddKernel (zpowers (actors.x:G))⊔
      (normalizer (zpowers (actors.x:G):Set G)⊓centralizer z))
    (hD:Nat.card (CubicLine.oddKernel (zpowers (actors.x:G)))=243)
    (he:IsExtraspecial 3 (CubicLine.oddKernel (zpowers (actors.x:G)))) :
    let V:=CubicNormalizer.oddKernel ((P:Subgroup (centralizer z)).map (centralizer z).subtype)
    let W:=zpowers (actors.x:G)
    let S:=V⊔CubicLine.oddKernel W
    S≤normalizer (V:Set G) ∧ ⁅S,S⁆≤V ∧
    ∀x∈S,x∉V→
      Nat.card (V⊓Subgroup.centralizer ({x}:Set G):Subgroup G)=9 ∧
      S≤normalizer ((V⊓Subgroup.centralizer ({x}:Set G):Subgroup G):Set G) ∧
      W≤V⊓Subgroup.centralizer ({x}:Set G) := by
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
  have hX:Nat.card X=9:=h.cubic_sylow_image_card P
  have hXH:X≤centralizer z:=map_subtype_le _
  have hXV:X≤V:=CubicNormalizer.le_oddKernel X hX (h.toCentralizerHypothesis.cubic_centralizer X hX hXH)
  have hWV:W≤V:=hWX.trans hXV
  obtain ⟨hV,hVc⟩:=h.original_cubic_kernel_eighty_one P
  let :IsElementaryAbelian 3 V:=hV
  let :IsExtraspecial 3 D:=he
  have hI:Nat.card (V⊓D:Subgroup G)=27:=
    (h.cubic_line_kernel_intersection X W hX hXH hW hWX hfixed hsplit hV hVc).2
  have hVW:V≤Subgroup.centralizer (W:Set G):=
    (map_subtype_le _:V≤Subgroup.centralizer (X:Set G)).trans (centralizer_le hWX)
  have hVD:V≤normalizer (D:Set G):=(hVW.trans (centralizer_le_normalizer _)).trans
    (CubicLine.normalizer_normalizes_oddKernel W)
  have hDV:D≤normalizer (V:Set G):=(cubic_extraspecial_intersection_and_normalizer V D hD hI hVD).2
  have hcom:⁅D,D⁆≤W:=(h.cubic_line_oddKernel_inversion W hW (hWX.trans hXH) hfixed).2
  have hcen:W≤Subgroup.centralizer (D:Set G):=le_centralizer_iff.mp (CubicLine.oddKernel_centralizes W hW)
  have hSN:V⊔D≤normalizer (V:Set G):=sup_le V.le_normalizer hDV
  have hSS:⁅V⊔D,V⊔D⁆≤V:=commutator_sup_le_of_normalized_derived V D hDV (hcom.trans hWV)
  have hSW:V⊔D≤Subgroup.centralizer (W:Set G):=sup_le hVW (CubicLine.oddKernel_centralizes W hW)
  refine ⟨hSN,hSS,?_⟩
  intro x hx hxV
  refine ⟨cubic_sup_outside_fixed_nine V D W hD hI hVD hW hcom hcen
    (h.cubic_line_marked_outside_fixed P actors ha hsplit hD) x hx hxV,
    abelian_quotient_preserves_fixed (V⊔D) V hSN hSS x hx,?_⟩
  exact le_inf hWV (fun w hw=>mem_centralizer_singleton_iff.mpr (hSW hx w hw))
end Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
