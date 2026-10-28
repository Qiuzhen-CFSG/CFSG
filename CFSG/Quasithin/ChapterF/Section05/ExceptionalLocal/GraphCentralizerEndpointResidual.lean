module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.GraphCentralizerAlternating
public import CFSG.Quasithin.ChapterI.Section04To05.Dihedral.EightSubgroup
/-!
# The endpoint-generated two-residual is the graph-centralizer residual

The endpoint Klein four-groups lie in O²(D), and their cubic conjugators
remain in O²(D). Thus its literal image in O²(C_G(f)/⟨f⟩) contains the
residual Sylow subgroup and fuses its involutions. The A₆ subgroup criterion
makes that image the entire residual. The already faithful quotient map
then gives O²(D)=O²(C_G(f)) as actual ambient subgroups, and identifies the
original O²(D) with A₆.

Source: Aschbacher–Smith F.5.5, printed p.302.
-/
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open GreenBook.LieModels.UnitaryFour
open ResidualJoinModel
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G)

omit [Finite G] in
theorem source_Dendpoint_le_D (b : Bool) : Dendpoint c i b ≤ D c i := by
  cases b
  · exact le_sup_left
  · exact le_sup_right

omit [Finite G] in
theorem source_endpointResidual_le_DtwoResidual (b : Bool) :
    (pResidual 2 (Dendpoint c i b)).map (Dendpoint c i b).subtype ≤ DtwoResidual c i := by
  rintro _ ⟨a,ha,rfl⟩
  let j : Dendpoint c i b →* D c i := inclusion (source_Dendpoint_le_D c i b)
  exact ⟨j a,map_pResidual_le 2 j (mem_map_of_mem j ha),rfl⟩

omit [Finite G] in
theorem sourceResidualJoin_le_DtwoResidual : sourceResidualJoin c i ≤ DtwoResidual c i := by
  apply sup_le
  · rintro _ ⟨a,ha,rfl⟩
    exact source_endpointResidual_le_DtwoResidual c i false ⟨a.val,a.property,rfl⟩
  · rintro _ ⟨a,ha,rfl⟩
    exact source_endpointResidual_le_DtwoResidual c i true ⟨a.val,a.property,rfl⟩

omit [Finite G] in
theorem source_DtwoResidual_le_centralizer_residual :
    DtwoResidual c i ≤ (pResidual 2 (C c i)).map (C c i).subtype := by
  rintro _ ⟨a,ha,rfl⟩
  let j : D c i →* C c i := inclusion (D_le_C c i)
  exact ⟨j a,map_pResidual_le 2 j (mem_map_of_mem j ha),rfl⟩

theorem sourceResidualJoin_involution_conjugate_in_DtwoResidual
    (hi : Function.Injective i) (x : G) (hx : x∈sourceResidualJoin c i)
    (hx2 : x^2=1) (hx1 : x≠1) :
    ∃ g∈DtwoResidual c i, g*x*g⁻¹=sourceHom c i (.r 2) := by
  rw [sourceResidualJoin_eq_range c i hi] at hx
  obtain ⟨a,rfl⟩ := hx
  have ha2 : a^2=1 := sourceHom_injective c i hi (by simpa only [map_pow,map_one] using hx2)
  have hz1 : sourceHom c i (.r 2)≠1 := by
    intro hh
    exact common_center_mem.2.2 (sourceHom_injective c i hi (hh.trans (map_one _).symm))
  have hf (b : Bool) (ha : sourceHom c i a∈sourceEndpointResidualCore c i b)
      (hz : sourceHom c i (.r 2)∈sourceEndpointResidualCore c i b) :
      ∃g∈DtwoResidual c i, g*sourceHom c i a*g⁻¹=sourceHom c i (.r 2) := by
    obtain ⟨g,hg,he⟩ :=
      sourceEndpointResidualCore_conjugate_in_residual c i hi b _ ha hx1 _ hz hz1
    exact ⟨g,source_endpointResidual_le_DtwoResidual c i b hg,he⟩
  rcases involution_mem_four a ha2 with hp | hp
  · apply hf false
    · rw [sourceEndpointResidualCore_point c i hi]
      exact mem_map_of_mem _ hp
    · rw [sourceEndpointResidualCore_point c i hi]
      exact mem_map_of_mem _ common_center_mem.1
  · apply hf true
    · rw [sourceEndpointResidualCore_plane c i hi]
      exact mem_map_of_mem _ hp
    · rw [sourceEndpointResidualCore_plane c i hi]
      exact mem_map_of_mem _ common_center_mem.2.1

/-- Inclusion of the endpoint-generated residual into the actual centralizer residual. -/
def sourceDResidualCentralizerMap : pResidual 2 (D c i) →* pResidual 2 (C c i) :=
  (((inclusion (D_le_C c i)).comp (pResidual 2 (D c i)).subtype)).codRestrict _
    (fun x => map_pResidual_le 2 (inclusion (D_le_C c i))
      (mem_map_of_mem _ x.property))

/-- The literal graph quotient restricted to the endpoint-generated residual. -/
def sourceDResidualGraphMap : pResidual 2 (D c i) →* pResidual 2 (graphCentralQuotient c i) :=
  (((QuotientGroup.mk' (zpowers (graphInCentralizer c i))).comp
    ((pResidual 2 (C c i)).subtype.comp (sourceDResidualCentralizerMap c i)))).codRestrict _
    (fun x => map_pResidual_le 2 (QuotientGroup.mk' (zpowers (graphInCentralizer c i)))
      (mem_map_of_mem (QuotientGroup.mk' (zpowers (graphInCentralizer c i)))
        (sourceDResidualCentralizerMap c i x).property))

omit [Finite G] in
theorem sourceResidualJoinQuotient_le_DResidualGraph :
    (sourceResidualJoinQuotient c i).subgroupOf (pResidual 2 (graphCentralQuotient c i)) ≤
      (sourceDResidualGraphMap c i).range := by
  intro x hx
  obtain ⟨a,ha,he⟩ := hx
  obtain ⟨d,hd,hda⟩ := sourceResidualJoin_le_DtwoResidual c i ha
  refine ⟨⟨d,hd⟩,Subtype.ext ?_⟩
  change QuotientGroup.mk' _ (inclusion (D_le_C c i) d) = x.val
  exact (congrArg (QuotientGroup.mk' _) (Subtype.ext hda)).trans he

theorem sourceResidualJoinQuotient_conjugate_in_DResidualGraph
    (hi : Function.Injective i) (x : sourceResidualJoinQuotient c i) (hx2 : orderOf x=2) :
    ∃ g∈(sourceDResidualGraphMap c i).range,
      g*(⟨x.val,sourceResidualJoinQuotient_le_twoResidual c i x.property⟩ :
        pResidual 2 (graphCentralQuotient c i))*g⁻¹ =
      ⟨sourceResidualQuotientCenter c i hi,sourceResidualJoinQuotient_le_twoResidual c i
        (sourceResidualQuotientCenter_mem c i hi)⟩ := by
  let q := QuotientGroup.mk' (zpowers (graphInCentralizer c i))
  obtain ⟨a,ha,he⟩ := x.property
  let u : sourceResidualJoin c i := ⟨a.val,ha⟩
  let qU := sourceOrdinaryGraphQuotientMap c i (sourceResidualJoin c i) (sourceResidualJoin_le_C c i)
  have hqU : Function.Injective qU := sourceOrdinaryGraphQuotientMap_injective c i hi _
    (sourceResidualJoin_le_ordinary c i hi) (sourceResidualJoin_le_C c i)
  have hqa : orderOf (q a)=2 := by rw [he]; exact (orderOf_coe x).trans hx2
  have huo : orderOf u=2 := (orderOf_injective qU hqU u).symm.trans hqa
  have hao : orderOf a.val=2 := (orderOf_coe u).trans huo
  have ha2 : a.val^2=1 := by rw [←hao]; exact pow_orderOf_eq_one _
  have ha1 : a.val≠1 := by intro hh; rw [hh,orderOf_one] at hao; omega
  obtain ⟨g,⟨gD,hgD,hg⟩,hconj⟩ :=
    sourceResidualJoin_involution_conjugate_in_DtwoResidual c i hi a.val ha ha2 ha1
  let gC := inclusion (D_le_C c i) gD
  let gW := sourceDResidualGraphMap c i ⟨gD,hgD⟩
  have hC : gC*a*gC⁻¹=sourceResidualCenterInC c i hi := by
    apply Subtype.ext
    change gD.val*a.val*gD.val⁻¹=sourceHom c i (.r 2)
    change gD.val=g at hg
    rw [hg]
    exact hconj
  refine ⟨gW,⟨⟨gD,hgD⟩,rfl⟩,?_⟩
  apply Subtype.ext
  change q gC*x.val*(q gC)⁻¹=q (sourceResidualCenterInC c i hi)
  rw [←he,←map_inv,←map_mul,←map_mul,hC]

variable (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z)
include h

theorem source_DResidualGraphMap_surjective (R : Sylow 2 (C c i)) (hR : Tf c i ≤ R) :
    Function.Surjective (sourceDResidualGraphMap c i) := by
  let W := pResidual 2 (graphCentralQuotient c i)
  let U := sourceResidualJoinQuotient c i
  have hUW : U ≤ W := sourceResidualJoinQuotient_le_twoResidual c i
  let v : U := ⟨sourceResidualQuotientCenter c i h.embedding_injective,
    sourceResidualQuotientCenter_mem c i h.embedding_injective⟩
  let vW : W := ⟨v.val,hUW v.property⟩
  let eU := sourceResidualJoinQuotientEquiv c i h.embedding_injective
  have hv2 : orderOf v=2 := by
    rw [←eU.orderOf_eq v,sourceResidualJoinQuotientEquiv_center c i h.embedding_injective]
    exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)
  have hvW2 : orderOf vW=2 := (orderOf_coe vW).symm.trans ((orderOf_coe v).trans hv2)
  obtain ⟨P,hP⟩ := source_graph_residual_sylow c i z h R hR
  change (P : Subgroup W).map W.subtype=U at hP
  let q := QuotientGroup.mk' (zpowers (graphInCentralizer c i))
  let S := R.mapSurjective (f:=q) (QuotientGroup.mk'_surjective _)
  have hUS : U ≤ S := sourceResidualJoinQuotient_le_R c i h.embedding_injective R hR
  have hInt : (S : Subgroup (graphCentralQuotient c i)) ⊓ W=U := by
    obtain ⟨Q,hQ⟩ := S.exists_sylow_map_eq_inf_of_normal W
    apply (eq_of_le_of_card_ge (le_inf hUS hUW) ?_).symm
    rw [←hQ,card_map_of_injective W.subtype_injective]
    rw [←hP,card_map_of_injective W.subtype_injective]
    exact (Nat.card_congr (Sylow.equiv Q P).toEquiv).le
  have hmem (x : W) : x.val ∈ U ↔ x ∈ (P : Subgroup W) := by
    rw [←hP]
    exact mem_map_iff_mem W.subtype_injective
  have hcent : centralizer ({vW} : Set W) = (P : Subgroup W) := by
    ext x
    have hh : x∈centralizer ({vW} : Set W) ↔
        x.val∈centralizer ({v.val} : Set (graphCentralQuotient c i)) := by
      simp only [mem_centralizer_singleton_iff]
      exact Subtype.ext_iff
    rw [hh,source_residual_center_centralizer c i z h R hR,←hmem]
    constructor
    · intro hx
      exact hInt ▸ (show x.val∈(S:Subgroup (graphCentralQuotient c i))⊓W from ⟨hx,x.property⟩)
    · intro hx
      exact hUS hx
  let eP : P ≃* DihedralGroup 4 :=
    ((P : Subgroup W).equivMapOfInjective W.subtype W.subtype_injective).trans
      ((MulEquiv.subgroupCongr hP).trans eU)
  let J := (sourceDResidualGraphMap c i).range
  have hPJ : (P : Subgroup W) ≤ J := by
    intro x hx
    exact sourceResidualJoinQuotient_le_DResidualGraph c i ((hmem x).mpr hx)
  have hf (x : P) (hx : orderOf x=2) : ∃g∈J,g*x.val*g⁻¹=vW := by
    let y : U := ⟨x.val.val,(hmem x.val).mpr x.property⟩
    have hy : orderOf y=2 := (orderOf_coe y).symm.trans
      ((orderOf_coe x.val).trans ((orderOf_coe x).trans hx))
    exact sourceResidualJoinQuotient_conjugate_in_DResidualGraph c i h.embedding_injective y hy
  obtain ⟨eW⟩ := source_graph_residual_alternating c i z h R hR
  have ht : J=⊤ :=
    DihedralInvolutionCentralizerHypotheses.subgroup_eq_top_of_sylow_involution_fusion
      eW P eP vW hvW2 hcent J hPJ hf
  exact MonoidHom.range_eq_top.mp ht

theorem source_DResidualCentralizerMap_surjective (R : Sylow 2 (C c i)) (hR : Tf c i ≤ R) :
    Function.Surjective (sourceDResidualCentralizerMap c i) := by
  obtain ⟨e,he⟩ := source_centralizer_residual_quotient_equiv c i z h R hR
  intro x
  obtain ⟨y,hy⟩ := source_DResidualGraphMap_surjective c i z h R hR (e x)
  refine ⟨y,e.injective (Subtype.ext ?_)⟩
  rw [he]
  exact congrArg Subtype.val hy

/-- The original two-residual equality, retaining both ambient subgroup inclusions. -/
theorem source_DtwoResidual_eq_centralizer_residual (R : Sylow 2 (C c i)) (hR : Tf c i ≤ R) :
    DtwoResidual c i = (pResidual 2 (C c i)).map (C c i).subtype := by
  apply le_antisymm (source_DtwoResidual_le_centralizer_residual c i)
  rintro _ ⟨x,hx,rfl⟩
  obtain ⟨y,hy⟩ := source_DResidualCentralizerMap_surjective c i z h R hR ⟨x,hx⟩
  refine ⟨y.val,y.property,?_⟩
  exact congrArg (fun a : pResidual 2 (C c i) => a.val.val) hy

theorem source_D_residual_alternating (R : Sylow 2 (C c i)) (hR : Tf c i ≤ R) :
    Nonempty (pResidual 2 (D c i) ≃* alternatingGroup (Fin 6)) := by
  have hi : Function.Injective (sourceDResidualCentralizerMap c i) := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : pResidual 2 (C c i) => x.val.val) hab
  let e := MulEquiv.ofBijective (sourceDResidualCentralizerMap c i)
    ⟨hi,source_DResidualCentralizerMap_surjective c i z h R hR⟩
  obtain ⟨eA⟩ := source_centralizer_residual_alternating c i z h R hR
  exact ⟨e.trans eA⟩

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
