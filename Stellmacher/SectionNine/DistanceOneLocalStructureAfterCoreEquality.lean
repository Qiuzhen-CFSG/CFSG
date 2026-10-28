module

public import Stellmacher.SectionNine.DistanceOneMaximalV1Elementary
public import Stellmacher.SectionNine.DistanceOneMaximalV1Order
public import Stellmacher.SectionNine.DistanceOneMaximalV1
public import Stellmacher.SectionNine.DistanceOneExtractedQuaternionProduct
public import Stellmacher.SectionNine.DistanceOneTerminalCoreOrder
public import Stellmacher.SectionNine.DistanceOneTerminalNormalEightQuotient
public import Stellmacher.SectionNine.DistanceOneProductConjugateClosure
public import Theory.GroupTheory.QuaternionElementaryEightCentralizer
public import Theory.GroupTheory.ElementaryEightCentralizerOrder

/-!
# The complete local structure after initial core equality

In the actual critical-length-one configuration, the faithful initial action,
initial core equality Q_a=Z_a, and final extracted intersection from source(8)
imply the full local conclusion. The actual ActionData and exact intersection
remain explicit. This module supplies both stabilizer core quotients, the
common Sylow order128, and the quaternion product on the literal Vstar.

The extracted product has center order2, quaternion factors and order32.
The first faithful quotient gives its Sylow order; the terminal core has
order64 by the primitive Klein exclusion. The maximal-V₁ construction and
its actual quotient action give a normal elementary subgroup U of order8
inside the product. Quaternion selfcentrality and the central-line action
bound give C_Q(U) order16. The native normal-eight recognition therefore
identifies the terminal core quotient with SL2(2). Finally that quotient
identifies the extracted product with the exact terminal conjugate closure,
so the original local conclusion assembles without replacing Vstar.

Source: Stellmacher(9.1), Journal of Algebra190 (1997), p.48 after (11).
The faithful, chief-factor and final-intersection producers supply the
explicit inputs; no later numbered theorem or local conclusion is used.
-/

namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem distance_one_local_structure_of_core_eq_center
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length=1)
    (hfaith : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (hcore : QAt ctx.Γ ctx.criticalPath.a=ZAt ctx.Γ ctx.criticalPath.a)
    (data : DistanceOneActionData ctx)
    (hintersection : z ctx.Γ ctx.criticalPath.a⊓stabilizer ctx.Γ (ctx.Γ.act data.x⁻¹ ctx.criticalPath.a)=
      z ctx.Γ ctx.criticalPath.a⊓q ctx.Γ ctx.criticalPath.a') :
    DistanceOneLocalConclusion ctx.toLocalContext := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let next := Γ.act data.x⁻¹ cp.a
  let C := z Γ cp.a⊓stabilizer Γ next
  let D := z Γ next⊓stabilizer Γ cp.a
  let V := C⊔D
  let Z := z Γ cp.a'
  let Q := q Γ cp.a'
  let Za := z Γ cp.a
  let P := stabilizer Γ cp.a'
  have hgeom := distance_one_local_geometry ctx hb data
  have hfour : 4≤(V⊓q Γ cp.a).relIndex V := by
    have hh := Subgroup.relIndex_mul_relIndex (⊥:Subgroup G) (V⊓q Γ cp.a) V bot_le inf_le_left
    simp only [Subgroup.relIndex_bot_left] at hh
    have hp : 0<Nat.card (V⊓q Γ cp.a:Subgroup G) := Nat.card_pos
    have hbound : 4*Nat.card (V⊓q Γ cp.a:Subgroup G)≤Nat.card V := hgeom.2.2
    nlinarith
  obtain ⟨hcenter,hZcard,hCcard,hDcard,hVcard⟩ := distance_one_extracted_product_center_card
    ctx hb hfaith data.toDistanceOneExtractionData data.coatom_stabilizer hfour hgeom.1
  have hVmodel := distance_one_extracted_quaternion_product ctx hb hfaith data
  have hVQ := distance_one_product_le_next_core ctx hb data.toDistanceOneExtractionData hintersection
  change V≤Q at hVQ
  change Nat.card V=32 at hVcard
  change Nat.card C=8 at hCcard
  change Nat.card Z=2 at hZcard
  change IsCentralProductQ8Q8 V at hVmodel
  have hseed : Za⊓Q≤V := by
    change Za⊓Q≤C⊔D
    rw [← hintersection]
    exact le_sup_left
  have hseedcard : Nat.card (Za⊓Q:Subgroup G)=8 := by
    rw [← hintersection]
    exact hCcard
  obtain ⟨hfirst,hTcard⟩ := distance_one_first_core_quotient_of_core_eq_center
    ctx.toLocalContext hb hfaith hcore
  have hQcard := distance_one_terminal_core_card_of_quaternion_product
    ctx.toLocalContext hb (show Nat.card T=128 from hTcard) V hVmodel hVQ hseed hseedcard
  obtain ⟨hZZ, U,hUQ,hZU,hUQc,hUE,hgreat,hUT,hUn,hlo,hnot,hUsup,hlow,hupper,_⟩ :=
    distance_one_maximal_v1_of_extraction ctx hb hfaith data.toDistanceOneExtractionData
      data.coatom_stabilizer hfour hgeom.1 hintersection
  rw [CosetGraphContext.e,ctx.Γ.twoResidualAt_def] at hUE
  have hZZa : Z≤Za := by
    change z ctx.Γ ctx.criticalPath.a'≤z ctx.Γ ctx.criticalPath.a
    rw [← hZZ]
    exact inf_le_left
  have hfactors := distance_one_product_factors Γ cp.a next
  have hIZ : V⊓Za=C := hfactors.2.2.2.1
  have hIcard : Nat.card (V⊓Za:Subgroup G)=8 := by rw [hIZ]; exact hCcard
  have hUsup' : U≤V⊔Za := by
    change U≤V⊔q Γ cp.a at hUsup
    change q Γ cp.a=z Γ cp.a at hcore
    rwa [hcore] at hUsup
  obtain ⟨hUV,hUcard⟩ := distance_one_v1_card_eight_of_core_eq_center
    ctx hb hfaith hcore U V hUQ hZU hUQc hUE hUT hUn hlow hupper
    hVQ hVcard hQcard hIcard hseed hUsup' hZcard hZZa
  have hEV : data.E≤Subgroup.normalizer (V:Set G) := by
    apply Subgroup.le_normalizer_iff_commutator_le_left.mpr
    exact (Subgroup.commutator_mono le_sup_left le_rfl).trans data.product_action
  have hZaE : Za≤data.E := by rw [data.generated]; exact le_sup_left
  have hZaV : Za≤Subgroup.normalizer (V:Set G) := hZaE.trans hEV
  let _ : IsElementaryAbelian 2 U := distance_one_v1_elementary_of_card_eight ctx hb U V
    hUQ hZU hUQc hUE hUT hUn hlow hupper hUcard hZcard hUV hVmodel hVcard hIcard hZaV
  have hself : V⊓Subgroup.centralizer (U:Set G)=U := by
    obtain ⟨L,R,hL,hR,hjoin,hinter,hcomm,_⟩ := hVmodel
    rw [hjoin]
    exact Subgroup.inf_centralizer_elementary_eight_of_quaternion_factors L R U
      hL hR hinter hcomm hUcard (hUV.trans_eq hjoin)
  have hend : cp.a'=cp.firstStep := by
    rw [← cp.path_end,← cp.path_first]
    congr 1
    exact Fin.ext hb
  have hZcentral : Z≤Subgroup.centralizer (P:Set G) := by
    have h75 := (lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).next_center.2
    rw [← hend] at h75
    change z Γ cp.a'≤_
    rw [h75]
    exact (omegaOneCenter_le_centerAmbient P).trans (centerAmbient_le_centralizer P)
  have hQP : Q≤P := by
    change q Γ cp.a'≤stabilizer Γ cp.a'
    rw [q,Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hQZ : Q≤Subgroup.centralizer (Z:Set G) :=
    hQP.trans (Subgroup.le_centralizer_iff.mp hZcentral)
  have hCcard := Subgroup.card_inf_centralizer_eq_sixteen_of_index_two Q V U Z hVQ
    hUcard hVcard hQcard hZU hZcard (by rw [Subgroup.commutator_comm]; exact hUQc.le)
    hQZ hself
  have hPU : P≤Subgroup.normalizer (U:Set G) := by
    have hSyl := (edge_sylow_data ctx.sectionSeven Γ cp).2
    rw [← hend] at hSyl
    change stabilizer Γ cp.a'≤Subgroup.normalizer (U:Set G)
    rw [← twoResidualIn_sup_sylow hSyl]
    exact sup_le (Subgroup.le_normalizer_iff_commutator_le_left.mpr hUE.le)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hUT).mp hUn)
  have hterminal := distance_one_terminal_quotient_of_normal_eight ctx.toLocalContext hb
    (show Nat.card T=128 from hTcard) hQcard U hUQ hZU hPU hUcard hZcard hUQc.le hCcard
  have hclosure := distance_one_extracted_product_eq_vstar_of_terminal_quotient ctx hb hfaith data
    (show Nat.card T=128 from hTcard) hterminal hintersection
  refine ⟨hfirst,hterminal,hTcard,hcore,?_⟩
  change IsCentralProductQ8Q8 (Stellmacher.SectionsFiveToSeven.conjugateClosure
    (z ctx.Γ ctx.criticalPath.a⊓q ctx.Γ ctx.criticalPath.a')
    (stabilizer ctx.Γ ctx.criticalPath.a'))
  have heq : V=Stellmacher.SectionsFiveToSeven.conjugateClosure
      (z ctx.Γ ctx.criticalPath.a⊓q ctx.Γ ctx.criticalPath.a')
      (stabilizer ctx.Γ ctx.criticalPath.a') := hclosure
  rw [← heq]
  exact hVmodel
end Stellmacher.SectionNine
