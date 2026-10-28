module
public import Stellmacher.SectionTen.TenOneSmallCoatomCentralizer
public import Stellmacher.SectionTen.TenOneSmallMiddleCoreClassTwo
public import Stellmacher.SectionNine.VertexNormalizedTwoSubgroupSolvable
public import Stellmacher.SectionNine.AmbientEdgeSylow
public import Stellmacher.SectionOne.QuadraticConjugateClosure

/-!
# The lower-mixed-core terminal-center closure

In the small first-module case, take the actual ambient normalizer N of
the mapped Wstar. Let L be the image of the lower mixed core O_{2,2'}(N),
and let U be its join with the mapped terminal edge stabilizer. The
U-conjugate closure of the mapped terminal center lies in the mapped
middle center. All subgroups remain in the original ambient group H.

The vertex-normalized-two-subgroup theorem makes N solvable. Wstar is
normal elementary and contains the terminal center, so the closure is an
elementary U-module. The actual ambient edge Sylow restricts to U, and
the lower mixed core supplies its normal two-layer and odd quotient.
The terminal center is fixed by this Sylow. The middle core lies in it
and acts quadratically by the proved central commutator bound. Pulling
any coatom back through the supplied injective embedding applies the
native Wstar centralizer bound. The general quadratic-conjugate-closure
result then gives the required containment.

Source: Stellmacher (10.1)(a3), printed pp.61–62, assertion (9),
`refs/files/stellmacher-n-group.pdf`. The source uses the lower mixed
core and the terminal edge; neither the upper residual nor the initial
edge replaces them. The final normalizer transfer is a separate theorem.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_small_mixed_closure_le_center
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    let W0 := NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓
      GeneratedNeighborhoodV ctx.Γ middle
    let Wstar := QAt ctx.Γ middle ⊓ Subgroup.centralizer (W0 : Set G)
    let N := Subgroup.normalizer (Wstar.map embedding : Set H)
    let L := ((pPrimeCore 2 (N ⧸ pCore 2 N)).comap
      (QuotientGroup.mk' (pCore 2 N))).map N.subtype
    let U := L ⊔ (GAt ctx.Γ middle ⊓ GAt ctx.Γ ctx.criticalPath.a').map embedding
    Stellmacher.conjugateClosure ((ZAt ctx.Γ ctx.criticalPath.a').map embedding) U ≤
      (ZAt ctx.Γ middle).map embedding := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let W0 := NeighborhoodQIntersection Γ (Neighborhood Γ middle) ⊓ GeneratedNeighborhoodV Γ middle
  let Wstar := QAt Γ middle ⊓ Subgroup.centralizer (W0 : Set G)
  let W := Wstar.map embedding
  let N := Subgroup.normalizer (W : Set H)
  let Rn := pCore 2 N
  let quotient : N →* N ⧸ Rn := QuotientGroup.mk' Rn
  let Ln := (pPrimeCore 2 (N ⧸ Rn)).comap quotient
  let R := Rn.map N.subtype
  let L := Ln.map N.subtype
  let edge := GAt Γ middle ⊓ GAt Γ cp.a'
  let E := edge.map embedding
  let U := L ⊔ E
  let Z := (ZAt Γ middle).map embedding
  let Bseed := (ZAt Γ cp.a').map embedding
  let V := Stellmacher.conjugateClosure Bseed U
  let Q := (QAt Γ middle).map embedding
  have hb : 1 < cp.length := by have := ctx.critical_length; change 1 < ctx.criticalPath.length; omega
  have hadj := (sectionTenOpeningGeometry ctx middle hpath).2.2.1
  have hpacket := ten_one_small_centralizer_elementary ctx middle hpath hsmall hmodel
  change GAt Γ middle ≤ normalizer (Wstar:Set G) ∧ _ at hpacket
  let _ : IsElementaryAbelian 2 Wstar := hpacket.2.1
  have hWne : Wstar ≠ ⊥ := by
    intro hh
    have hc := hpacket.2.2.1
    change Nat.card Wstar=8 ∨ Nat.card Wstar=16 at hc
    rw [hh,card_bot] at hc
    omega
  let _ : Group.IsSolvable N := ambient_vertex_normalized_two_subgroup_solvable
    ctx.toAmbientSectionNineContext middle Wstar hWne
      (IsElementaryAbelian.isPGroup 2 Wstar) hpacket.1
  have hMN : (GAt Γ middle).map embedding ≤ N :=
    (map_mono hpacket.1).trans (Wstar.le_normalizer_map embedding)
  have hEN : E ≤ N := (map_mono inf_le_left).trans hMN
  have hUN : U ≤ N := sup_le (map_subtype_le _) hEN
  let _ : Group.IsSolvable U := Group.isSolvable_of_isSolvable_injective
    (inclusion_injective hUN)
  have hUP : U ≤ normalizer (W:Set H) := hUN
  have hZstar : ZAt Γ middle ≤ Wstar := hpacket.2.2.2.1.ge.trans inf_le_left
  have hBstar : ZAt Γ cp.a' ≤ Wstar :=
    ((sectionTenOpeningData ctx middle hpath).center_direct_product.1.ge.trans' le_sup_right).trans hZstar
  have hBW : Bseed ≤ W := map_mono hBstar
  have hVW : V ≤ W := by
    apply (closure_le _).mpr
    rintro x ⟨a,b,rfl⟩
    exact (mem_normalizer_iff.mp (hUP a.property) b).mp (hBW b.property)
  let _ : IsElementaryAbelian 2 W := IsElementaryAbelian.map embedding
  let _ : IsElementaryAbelian 2 V := {
    toIsMulCommutative := ⟨⟨fun x y => Subtype.ext
      (setLike_mul_comm (s:=W) (hVW x.property) (hVW y.property))⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun v =>
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (v:H) (hVW v.property))) }
  have hUV : U ≤ normalizer (V:Set H) := by
    rw [show V = closure {x:H | ∃ a:U, ∃ b:Bseed,x=(a:H)*(b:H)*(a:H)⁻¹} from rfl,
      le_normalizer_closure_iff]
    intro a ha x hx
    obtain ⟨b,v,rfl⟩ := hx
    apply Subgroup.subset_closure
    refine ⟨⟨a*(b:H),U.mul_mem ha b.property⟩,v,?_⟩
    simp only [mul_inv_rev]
    group
  have hBV : Bseed ≤ V := by
    intro b hb
    exact Subgroup.subset_closure ⟨1,⟨b,hb⟩,by simp⟩
  obtain ⟨Sedge,hSedge⟩ := ambient_edge_stabilizer_is_sylow_two
    ctx.toAmbientSectionNineContext hb middle cp.a' hadj
  change (Sedge:Subgroup H)=E at hSedge
  have hSU : (Sedge:Subgroup H) ≤ U := hSedge.le.trans le_sup_right
  let SU : Sylow 2 U := Sedge.subtype hSU
  have hSUmap : (SU:Subgroup U).map U.subtype=E := by
    change ((Sedge:Subgroup H).subgroupOf U).map U.subtype=E
    rw [map_subgroupOf_eq_of_le hSU,hSedge]
  have hRLn : Rn ≤ Ln := by
    intro r hr
    change quotient r ∈ pPrimeCore 2 (N ⧸ Rn)
    have heq : quotient r=1 := (QuotientGroup.eq_one_iff (N:=Rn) r).mpr hr
    rw [heq]
    exact one_mem _
  have hRL : R ≤ L := map_mono hRLn
  have hLU : L ≤ U := le_sup_left
  have hRU : R ≤ U := hRL.trans hLU
  have hNR : N ≤ normalizer (R:Set H) := by
    have hh := Rn.le_normalizer_map N.subtype
    rwa [normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype] at hh
  have hNL : N ≤ normalizer (L:Set H) := by
    have hh := Ln.le_normalizer_map N.subtype
    rwa [normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype] at hh
  let RU := R.subgroupOf U
  let LU := L.subgroupOf U
  let _ : RU.Normal := normal_subgroupOf_of_le_normalizer (hUN.trans hNR)
  let _ : LU.Normal := normal_subgroupOf_of_le_normalizer (hUN.trans hNL)
  have hRUtwo : IsPGroup 2 RU := (pCore_isPGroup.map N.subtype).comap_subtype
  have hRLU : RU ≤ LU := subgroupOf_mono U hRL
  have hodd : Nat.Coprime 2 (RU.relIndex LU) := by
    rw [relIndex_subgroupOf hLU]
    change Nat.Coprime 2 ((Rn.map N.subtype).relIndex (Ln.map N.subtype))
    rw [relIndex_map_map_of_injective _ _ N.subtype_injective]
    have hcard : Rn.relIndex Ln = Nat.card (pPrimeCore 2 (N ⧸ Rn)) := by
      have hh := Subgroup.relIndex_ker (K:=Ln) quotient
      rw [show quotient.ker=Rn from QuotientGroup.ker_mk' Rn,
        show Ln.map quotient=pPrimeCore 2 (N ⧸ Rn) from
          map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Rn) _] at hh
      exact hh
    rw [hcard]
    exact pPrimeCore_coprime_card
  have hsupp : (⊤:Subgroup U)=LU⊔(SU:Subgroup U) := by
    apply map_injective (f:=U.subtype) U.subtype_injective
    rw [← MonoidHom.range_eq_map,range_subtype,Subgroup.map_sup]
    change U=(L.subgroupOf U).map U.subtype ⊔ (SU:Subgroup U).map U.subtype
    rw [map_subgroupOf_eq_of_le hLU,hSUmap]
  have hseed : (SU:Subgroup U).map U.subtype ≤ centralizer (Bseed:Set H) := by
    rw [hSUmap]
    obtain ⟨actor,_,halign⟩ := lemma_seven_five_endpoint_alignment
      ctx.sectionSeven Γ cp ctx.commutator_eq
    have hh := nine_next_center_centralizes_stabilizer ctx.toLocalContext.toSectionNineLocalContext
      cp.a' ⟨actor,halign⟩
    exact (map_mono (show edge ≤ centralizer (ZAt Γ cp.a':Set G) from
      inf_le_right.trans hh)).trans (map_centralizer_le_centralizer_image _ _)
  have hQedge : QAt Γ middle ≤ edge := by
    refine le_inf ?_ ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core
      middle cp.a' ((mem_neighborhood_iff_adjacent Γ).mpr hadj) default).2.2
    change Γ.twoCoreAt middle ≤ Γ.stabilizer middle
    rw [Γ.twoCoreAt_def]
    exact map_subtype_le _
  have hQE : Q ≤ E := map_mono hQedge
  have hQU : Q ≤ U := hQE.trans le_sup_right
  let Y := Q.subgroupOf U
  have hYS : Y ≤ (SU:Subgroup U) := by
    intro y hy
    change (y:H) ∈ (Sedge:Subgroup H)
    exact hSedge.ge (hQE hy)
  have hYmap : Y.map U.subtype=Q := map_subgroupOf_eq_of_le hQU
  have hdouble : ⁅⁅V,Y.map U.subtype⁆,Y.map U.subtype⁆=⊥ := by
    rw [hYmap]
    have hQQ : ⁅Q,Q⁆ ≤ Z := by
      have hh := map_mono (f:=embedding)
        (ten_one_small_middle_core_commutator_le_center ctx middle hpath hsmall hmodel)
      rwa [map_commutator] at hh
    have hVQ : V ≤ Q := hVW.trans (map_mono (show Wstar≤QAt Γ middle from inf_le_left))
    have hZcentral : ZAt Γ middle ≤ centralizer (QAt Γ middle:Set G) := by
      rw [(sectionTenOpeningData ctx middle hpath).center_omega]
      exact (omegaOneCenter_le_centerAmbient _).trans (centerAmbient_le_centralizer _)
    have hZQ : Z ≤ centralizer (Q:Set H) :=
      (map_mono hZcentral).trans (map_centralizer_le_centralizer_image _ _)
    exact bot_unique ((commutator_mono ((commutator_mono hVQ le_rfl).trans hQQ) le_rfl).trans
      (commutator_eq_bot_iff_le_centralizer.mpr hZQ).le)
  have hfixed (F : Subgroup U) (hFY : F ≤ Y) (hindex : F.relIndex Y ≤ 2) :
      V ⊓ centralizer (F.map U.subtype:Set H) ≤ Z := by
    let D := F.map U.subtype
    let Dg := D.comap embedding
    have hDQ : D ≤ Q := (map_mono hFY).trans hYmap.le
    have hDgQ : Dg ≤ QAt Γ middle := by
      have hh := comap_mono (f:=embedding) hDQ
      rwa [comap_map_eq_self_of_injective ctx.embedding_injective] at hh
    have hDgmap : Dg.map embedding=D := map_comap_eq_self
      (hDQ.trans (map_le_range _ _))
    have hFQindex : (Dg.subgroupOf (QAt Γ middle)).index ≤ 2 := by
      change Dg.relIndex (QAt Γ middle) ≤ 2
      rw [← relIndex_map_map_of_injective _ _ ctx.embedding_injective,hDgmap]
      change D.relIndex Q ≤ 2
      rw [← hYmap,show D=F.map U.subtype from rfl,
        relIndex_map_map_of_injective _ _ U.subtype_injective]
      exact hindex
    have hc := ten_one_small_coatom_centralizer_le_center ctx middle hpath hsmall hmodel
      (Dg.subgroupOf (QAt Γ middle)) hFQindex
    change Wstar ⊓ centralizer (((Dg.subgroupOf (QAt Γ middle)).map
      (QAt Γ middle).subtype):Set G) ≤ ZAt Γ middle at hc
    rw [map_subgroupOf_eq_of_le hDgQ] at hc
    intro v hv
    obtain ⟨g,hg,rfl⟩ := hVW hv.1
    apply mem_map_of_mem embedding
    apply hc
    refine ⟨hg,?_⟩
    change g ∈ centralizer (Dg:Set G)
    rw [mem_centralizer_iff]
    intro d hd
    apply ctx.embedding_injective
    simpa only [map_mul] using mem_centralizer_iff.mp hv.2 (embedding d) hd
  change V ≤ Z
  exact SectionOne.quadratic_conjugate_closure_le_of_coatom_centralizers U V Z Bseed
    hUV hBV rfl RU LU hRUtwo hRLU hodd SU hsupp hseed Y hYS hdouble hfixed

end Stellmacher.SectionTen

