module
public import Stellmacher.SectionTen.TenOneMiddleCenterResidual
public import Stellmacher.SectionTen.TenOneMiddleResidualNeighborhood
public import Stellmacher.SectionTen.TenOneSmallNeighborhoodQuotient
public import Theory.GroupTheory.AbelianExponentFourRecognition

/-!
# An order-four element in the middle residual core

In the actual small-module, SL2(2) branch of Section Ten, an independently
established order-sixteen middle residual core contains an element of order
four. This is the remaining witness needed for its C4×C4 recognition; no
model for the residual core is assumed.

The core D lies in the order-thirty-two middle neighborhood U and is normal
in the middle stabilizer. Local transitivity and neighborhood generation
make every neighboring order-eight module escape D. Each module therefore
meets D exactly in the common four-center Z. The endpoint noncontainment
and module-centralizer bound supply noncommuting involutions from the two
endpoint modules. Both escape D, so their product belongs to D by index two.
It has nontrivial square; the elementary quotient U/Z and elementary Z
make its fourth power trivial. Thus its order is exactly four.

Source: the C4×C4 identification in Stellmacher (10.1)(a1), printed p.60 /
PDF p.50, `refs/files/stellmacher-n-group.pdf`. This supplies an explicit
witness for the source's residual-core recognition step.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
open scoped commutatorElement
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

set_option maxHeartbeats 800000 in
public theorem ten_one_middle_residual_order_four
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (hDcard : Nat.card (twoCoreIn (EAt ctx.Γ middle)) = 16) :
    ∃ x : twoCoreIn (EAt ctx.Γ middle), orderOf x = 4 := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let M := GAt Γ middle
  let U := GeneratedNeighborhoodV Γ middle
  let Z := ZAt Γ middle
  let E := EAt Γ middle
  let D := twoCoreIn E
  let V := VAt Γ cp.firstStep
  let V' := VAt Γ cp.a'
  have hopen := sectionTenOpeningData ctx middle hpath
  obtain ⟨_,hfirst,hterminal,_⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hfirstN := (mem_neighborhood_iff_adjacent Γ).mpr hfirst
  have hterminalN := (mem_neighborhood_iff_adjacent Γ).mpr hterminal
  have hb : 1 < cp.length := by change 1 < ctx.criticalPath.length; rw [ctx.critical_length]; decide
  have hVU {v : Γ.Vertex} (hv : v ∈ Neighborhood Γ middle) : VAt Γ v ≤ U :=
    le_sSup ⟨v,hv,rfl⟩
  have hZV {v : Γ.Vertex} (hv : v ∈ Neighborhood Γ middle) : Z ≤ VAt Γ v :=
    nine_seven_neighbor_center_le_module Γ
      (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hv))
  have hEM : E ≤ M := by
    change Γ.twoResidualAt middle ≤ M
    rw [Γ.twoResidualAt_def]
    exact twoResidualIn_le _
  have hE : E = twoResidualIn M := Γ.twoResidualAt_def middle
  have hDM : D ≤ M := (twoCoreIn_le E).trans hEM
  have hMD : M ≤ Subgroup.normalizer (D : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDM).mp
      (twoCoreIn_normal_of_normal E M hEM
        (hE ▸ twoResidualIn_normal M))
  have hDU : D ≤ U := ten_one_middle_residual_core_le_neighborhood ctx middle hpath hsmall hmodel
  have hZD : Z ≤ D := ten_one_middle_center_le_residual_core ctx middle hpath
  have hUcard : Nat.card U = 32 := ten_one_small_neighborhood_card ctx middle hpath hsmall
  have hZcard : Nat.card Z = 4 := hopen.center_card
  have hVcard (v : Γ.Vertex) (hv : v ∈ Neighborhood Γ middle) : Nat.card (VAt Γ v) = 8 := by
    obtain ⟨mover,hmove⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity
      middle hfirstN hv
    rw [← hmove,VAt,v_act]
    exact (Subgroup.card_map_of_injective (MulAut.conj (mover:G)⁻¹).injective).trans hsmall
  have hescape (v : Γ.Vertex) (hv : v ∈ Neighborhood Γ middle) : ¬ VAt Γ v ≤ D := by
    intro hVD
    have hUD : U ≤ D := by
      apply sSup_le
      rintro K ⟨w,hw,rfl⟩
      obtain ⟨mover,hmove⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity middle hv hw
      have hDmap : D.map (MulAut.conj (mover:G)⁻¹).toMonoidHom = D :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hMD (M.inv_mem mover.property))
      change CosetGraphContext.v Γ w ≤ D
      rw [← hmove,v_act,← hDmap]
      exact Subgroup.map_mono hVD
    have hcount := Subgroup.card_le_of_le hUD
    change Nat.card D = 16 at hDcard
    rw [hUcard,hDcard] at hcount
    omega
  have hintersection (v : Γ.Vertex) (hv : v ∈ Neighborhood Γ middle) : VAt Γ v ⊓ D = Z := by
    have hZI : Z ≤ VAt Γ v ⊓ D := le_inf (hZV hv) hZD
    have hIne : VAt Γ v ⊓ D ≠ VAt Γ v := by
      intro hh
      exact hescape v hv (hh ▸ (inf_le_right : VAt Γ v ⊓ D ≤ D))
    have hIlt : Nat.card (VAt Γ v ⊓ D : Subgroup G) < 8 := by
      rw [← hVcard v hv]
      have hle := Subgroup.card_le_of_le (inf_le_left : VAt Γ v ⊓ D ≤ VAt Γ v)
      by_contra hn
      exact hIne (Subgroup.eq_of_le_of_card_ge inf_le_left (by omega))
    have hdiv : Nat.card (VAt Γ v ⊓ D : Subgroup G) ∣ 8 :=
      (hVcard v hv) ▸ Subgroup.card_dvd_of_le (inf_le_left : VAt Γ v ⊓ D ≤ VAt Γ v)
    have hIlower : 4 ≤ Nat.card (VAt Γ v ⊓ D : Subgroup G) :=
      hZcard ▸ Subgroup.card_le_of_le hZI
    have hIcard : Nat.card (VAt Γ v ⊓ D : Subgroup G) = 4 := by
      interval_cases h : Nat.card (VAt Γ v ⊓ D : Subgroup G) <;> norm_num at *
    exact (Subgroup.eq_of_le_of_card_ge hZI (by rw [hIcard,hZcard])).symm
  let _ : IsElementaryAbelian 2 V :=
    ((lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).longer_case hb).1
  have helem (v : Γ.Vertex) (hv : v ∈ Neighborhood Γ middle) : IsElementaryAbelian 2 (VAt Γ v) := by
    obtain ⟨mover,hmove⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity middle hfirstN hv
    change IsElementaryAbelian 2 (CosetGraphContext.v Γ v)
    rw [← hmove,v_act]
    exact IsElementaryAbelian.map _
  let _ : IsElementaryAbelian 2 V' := helem cp.a' hterminalN
  have hZcentral : Z ≤ Subgroup.centralizer (U : Set G) := by
    change ZAt ctx.Γ middle ≤ Subgroup.centralizer (GeneratedNeighborhoodV ctx.Γ middle : Set G)
    rw [← ten_one_small_intersection ctx middle hpath hsmall]
    exact ten_one_common_intersection_centralizes ctx middle hpath
  have hnot : ¬ V ≤ Subgroup.centralizer (V' : Set G) :=
    fun h => hopen.first_noncontainment (h.trans hopen.endpoint_centralizer)
  obtain ⟨x,hxV,hxnot⟩ := SetLike.not_le_iff_exists.mp hnot
  rw [Subgroup.mem_centralizer_iff] at hxnot
  push Not at hxnot
  obtain ⟨y,hyV,hyx⟩ := hxnot
  have hxU : x ∈ U := hVU hfirstN hxV
  have hyU : y ∈ U := hVU hterminalN hyV
  have hxZ : x ∉ Z := fun hz => hyx
    (Subgroup.mem_centralizer_iff.mp (hZcentral hz) y hyU)
  have hyZ : y ∉ Z := fun hz => hyx
    (Subgroup.mem_centralizer_iff.mp (hZcentral hz) x hxU).symm
  have hxD : x ∉ D := fun hd => hxZ (hintersection cp.firstStep hfirstN ▸ ⟨hxV,hd⟩)
  have hyD : y ∉ D := fun hd => hyZ (hintersection cp.a' hterminalN ▸ ⟨hyV,hd⟩)
  have hindex : (D.subgroupOf U).index = 2 := by
    have hcount := (D.subgroupOf U).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDU).toEquiv,hDcard,hUcard] at hcount
    omega
  have hxyD : x*y ∈ D :=
    ((D.subgroupOf U).mul_mem_iff_of_index_two hindex
      (a:=⟨x,hxU⟩) (b:=⟨y,hyU⟩)).mpr (by change (x∈D ↔ y∈D); simp [hxD,hyD])
  have hx2 : x^2=1 := elemPow_eq_one_of_isElementaryAbelian (p:=2) (A:=V) x hxV
  have hy2 : y^2=1 := elemPow_eq_one_of_isElementaryAbelian (p:=2) (A:=V') y hyV
  have hxinv : x⁻¹=x := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hx2)
  have hyinv : y⁻¹=y := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hy2)
  have hxy2 : (x*y)^2 ≠ 1 := by
    intro hh
    have hi : (x*y)⁻¹=x*y := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hh)
    rw [mul_inv_rev,hxinv,hyinv] at hi
    exact hyx hi
  obtain ⟨hN,hW,_⟩ := ten_one_small_neighborhood_quotient_elementary ctx middle hpath hsmall
  let _ := hN
  let _ := hW
  let π : U →* U ⧸ Z.subgroupOf U := QuotientGroup.mk' (Z.subgroupOf U)
  have hsquareZ : (x*y)^2 ∈ Z := by
    have hh := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (U ⧸ Z.subgroupOf U)) (π ⟨x*y,U.mul_mem hxU hyU⟩)
    rw [← map_pow] at hh
    exact (QuotientGroup.eq_one_iff (N := Z.subgroupOf U) ((⟨x*y,U.mul_mem hxU hyU⟩ : U)^2)).mp hh
  let _ : IsElementaryAbelian 2 Z := by
    rw [show Z = omegaOneCenter (QAt Γ middle) from hopen.center_omega]
    exact omegaOneCenterAmbient_elementaryAbelian _
  have hxy4 : (x*y)^4=1 := by
    have hh := elemPow_eq_one_of_isElementaryAbelian (p:=2) (A:=Z) ((x*y)^2) hsquareZ
    simpa only [← pow_mul] using hh
  refine ⟨⟨x*y,hxyD⟩,orderOf_eq_four_of_fourth_power ?_ ?_⟩
  · exact Subtype.ext hxy4
  · intro hh
    exact hxy2 (congrArg Subtype.val hh)

end Stellmacher.SectionTen
