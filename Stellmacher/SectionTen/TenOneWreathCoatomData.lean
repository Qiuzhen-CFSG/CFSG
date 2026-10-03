module
public import Stellmacher.SectionTen.TenOneWreathFirstImage
public import Theory.ElementaryAbelian.Basic

/-!
# The normal four and fixed coatom in the wreath branch of (10.1)

Keep any supplied surjective quotient map from the terminal stabilizer with
kernel its actual two-core. Under the wreath alternative of (9.5), the image
of the first module is an elementary four normal in the actual middle-core
Sylow. The middle/terminal-core intersection has index dividing two in the
terminal core, and its commutator with the first module lies in the terminal
module.

The first-module kernel theorem and exact kernel-image index formula give
order four. The critical-length neighborhood containment puts this image
inside the middle-core Sylow, and ambient first-module invariance gives its
normality. The cubic middle quotient bounds the core-intersection index.
The commutator lies in both the first module and terminal core, hence in
the terminal module by the same kernel theorem.

Source: Stellmacher (10.1), printed p.60/PDF p.50, the paragraph excluding
case (5), `refs/files/stellmacher-n-group.pdf`. These are the geometric inputs
to the action on the Frattini quotient of Q/V; no replacement action or
chief-factor conclusion is assumed here.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
open scoped IsMulCommutative
universe u
set_option maxHeartbeats 800000 in
public theorem ten_one_wreath_coatom_data
    {H G K : Type u} [Group H] [Finite H] [Group G] [Finite G] [Group K] [Finite K]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (actor : G) (hactor : actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep)
    (hindex : QuotientCardEq
      (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
        ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2)
    (hlarge : Nat.card (VAt ctx.Γ ctx.criticalPath.a') = 2 ^ 5)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a')
      (QAt ctx.Γ ctx.criticalPath.a') SL2TwoWreathC2)
    (hIcard : Nat.card (VAt ctx.Γ ctx.criticalPath.a' ⊓
      VAt ctx.Γ ctx.criticalPath.firstStep : Subgroup G) = 2 ^ 3)
    (f : GAt ctx.Γ ctx.criticalPath.a' →* K) (hsurj : Function.Surjective f)
    (hkernel : f.ker = (QAt ctx.Γ ctx.criticalPath.a').subgroupOf
      (GAt ctx.Γ ctx.criticalPath.a')) :
    let J := ((VAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf
      (GAt ctx.Γ ctx.criticalPath.a')).map f
    ∃ sylow : Sylow 2 K,
      J ≤ sylow ∧ (J.subgroupOf (sylow : Subgroup K)).Normal ∧
      IsElementaryAbelian 2 J ∧ Nat.card J = 4 ∧
      (QAt ctx.Γ middle ⊓ QAt ctx.Γ ctx.criticalPath.a').relIndex
        (QAt ctx.Γ ctx.criticalPath.a') ∣ 2 ∧
      ⁅QAt ctx.Γ middle ⊓ QAt ctx.Γ ctx.criticalPath.a',
        VAt ctx.Γ ctx.criticalPath.firstStep⁆ ≤ VAt ctx.Γ ctx.criticalPath.a' := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.a'
  let U := VAt Γ cp.a'
  let C := VAt Γ cp.firstStep
  let Qm := QAt Γ middle
  let Qt := QAt Γ cp.a'
  let J := (C.subgroupOf P).map f
  have hb : 1 < cp.length := by have := ctx.critical_length; change 1 < ctx.criticalPath.length; omega
  have hb2 : 2 < cp.length := by have := ctx.critical_length; change 2 < ctx.criticalPath.length; omega
  obtain ⟨_, hfirst, hterminal, _⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hCP : C ≤ P := (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.2
  have hQmC : Qm ≤ Subgroup.normalizer (C : Set G) :=
    (((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core
      middle cp.firstStep ((mem_neighborhood_iff_adjacent Γ).mpr hfirst) default).2.2).trans
        (stabilizer_le_normalizer_v Γ cp.firstStep)
  have hCQm : C ≤ Qm :=
    (show C ≤ GeneratedNeighborhoodV Γ middle from le_sSup
      ⟨cp.firstStep, (mem_neighborhood_iff_adjacent Γ).mpr hfirst, rfl⟩).trans
        (nine_seven_neighborhood_le_own_core ctx.toLocalContext.toSectionNineLocalContext hb2 middle)
  have hpen : cp.path ⟨cp.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ = middle := by
    obtain ⟨i, hi, hmid⟩ := hpath
    rw [← hmid]
    apply congrArg cp.path
    apply Fin.ext
    change cp.length - 1 = i.val
    have hlen := ctx.critical_length
    change ctx.criticalPath.length - 1 = i.val
    omega
  have hfker : f.ker = pCore 2 P := by
    rw [hkernel]
    change (Γ.twoCoreAt cp.a').subgroupOf P = _
    rw [Γ.twoCoreAt_def]
    exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
  obtain ⟨sylow, hsylow⟩ := nine_nine_terminal_core_image_sylow
    ctx.toAmbientSectionNineContext hb f hsurj hfker
  change (sylow : Subgroup K) = ((QAt Γ (cp.path ⟨cp.length - 1,
    Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)).subgroupOf P).map f at hsylow
  rw [hpen] at hsylow
  have hJS : J ≤ (sylow : Subgroup K) := by
    rw [hsylow]
    exact Subgroup.map_mono (Subgroup.comap_mono hCQm)
  have hnormal : (sylow : Subgroup K) ≤ Subgroup.normalizer (J : Set K) := by
    rw [hsylow]
    apply le_trans (Subgroup.map_mono ?_) ((C.subgroupOf P).le_normalizer_map f)
    exact (Subgroup.comap_mono hQmC).trans (C.le_normalizer_comap P.subtype)
  let _ : IsElementaryAbelian 2 C :=
    ((lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).longer_case hb).1
  let _ : IsElementaryAbelian 2 (C.subgroupOf P) := IsElementaryAbelian.subgroupOf hCP
  have hinter : C ⊓ Qt = C ⊓ U :=
    ten_one_wreath_first_core_intersection ctx middle hpath actor hactor hindex hlarge hmodel hIcard
  have hCcard : Nat.card C = 32 :=
    (nine_seven_endpoint_module_card ctx.toLocalContext.toSectionNineLocalContext).trans hlarge
  have hIcard' : Nat.card (C ⊓ Qt : Subgroup G) = 8 := by
    rw [hinter]
    change Nat.card (U ⊓ C : Subgroup G) = 8 at hIcard
    simpa only [inf_comm] using hIcard
  have hJcard : Nat.card J = 4 := by
    rw [show J = (C.subgroupOf P).map f from rfl, ← Subgroup.relIndex_ker, hkernel,
      Subgroup.relIndex_subgroupOf hCP]
    change Qt.relIndex C = 4
    have hc := (Qt.subgroupOf C).index_mul_card
    have hkerCard : Nat.card (Qt.subgroupOf C) = 8 := by
      rw [← Subgroup.inf_subgroupOf_left Qt C,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show C ⊓ Qt ≤ C from inf_le_left)).toEquiv]
      exact hIcard'
    change Qt.relIndex C * Nat.card (Qt.subgroupOf C) = Nat.card C at hc
    rw [hkerCard, hCcard] at hc
    omega
  let edge := GAt Γ middle ⊓ P
  have hQtP : Qt ≤ P := by
    change Γ.twoCoreAt cp.a' ≤ P
    rw [Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hQmSelf : Qm ≤ GAt Γ middle := by
    change Γ.twoCoreAt middle ≤ GAt Γ middle
    rw [Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hQmP : Qm ≤ P := ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core
    middle cp.a' ((mem_neighborhood_iff_adjacent Γ).mpr hterminal) default).2.2
  have hQtMiddle : Qt ≤ GAt Γ middle := ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core
    cp.a' middle ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hterminal)) default).2.2
  have hEdgeCard : Nat.card edge = 2 * Nat.card Qm :=
    (cubic_local_action_of_sl2Two_quotient Γ ctx.sectionSeven middle
      (sectionTenOpeningData ctx middle hpath).quotient_model).edge_card _ hterminal
  have hEdgeIndex : Qm.relIndex edge = 2 := by
    have hcount := (Qm.subgroupOf edge).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_inf hQmSelf hQmP)).toEquiv] at hcount
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (hcount.trans hEdgeCard)
  have hcoatom : (Qm ⊓ Qt).relIndex Qt ∣ 2 := by
    rw [Subgroup.inf_relIndex_right]
    have hbound := Subgroup.relIndex_le_of_le_right (H := Qm) (le_inf hQtMiddle hQtP)
      (show Qm.relIndex edge ≠ 0 by rw [hEdgeIndex]; decide)
    rw [hEdgeIndex] at hbound
    have hpos : Qm.relIndex Qt ≠ 0 := Subgroup.index_ne_zero_of_finite
    interval_cases h : Qm.relIndex Qt <;> simp_all
  have hcomm : ⁅Qm ⊓ Qt, C⁆ ≤ U := by
    have hcommC : ⁅Qm ⊓ Qt, C⁆ ≤ C :=
      (Subgroup.commutator_mono inf_le_left le_rfl).trans
        (Subgroup.le_normalizer_iff_commutator_le_right.mp hQmC)
    have hcommQt : ⁅Qm ⊓ Qt, C⁆ ≤ Qt :=
      (Subgroup.commutator_mono inf_le_right le_rfl).trans
        (Subgroup.le_normalizer_iff_commutator_le_left.mp
          (hCP.trans (stabilizer_le_normalizer_q Γ cp.a')))
    exact (le_inf hcommC hcommQt).trans (hinter ▸ inf_le_right)
  exact ⟨sylow, hJS, (Subgroup.normal_subgroupOf_iff_le_normalizer hJS).mpr hnormal,
    IsElementaryAbelian.map f, hJcard, hcoatom, hcomm⟩
end Stellmacher.SectionTen
