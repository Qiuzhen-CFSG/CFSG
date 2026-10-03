module
public import Stellmacher.SectionTen.TenOneSmallSylowUpper
public import Stellmacher.SectionTen.TenOneSmallCommonCoreElementary
public import Theory.GroupTheory.CenterFreeC4SquareElementaryCentralizer

/-!
# The elementary centralizer Wstar in the small branch

For the order-eight first-module case with local quotient SL₂(2), let W₀
be the intersection of all middle-neighbor cores inside the generated middle
neighborhood, and put W*=C_Qmiddle(W₀). This actual W* is normalized by the
middle stabilizer and is elementary abelian of order eight or sixteen.
Moreover, W*∩O₂(Emiddle)=Zmiddle and [W*,Emiddle]≤Zmiddle.

Restrict the actual subgroups to the middle stabilizer. The native input
packet supplies its trivial center, C₄×C₄ residual-core intersection, and
residual image of order three. The previous common-core theorem gives a
normal elementary W₀ of order eight. The middle central four-subgroup lies
in every neighbor core and neighbor module, hence in W₀. The general
center-free C₄-square centralizer theorem now applies. An explicit subtype
calculation identifies its centralizer with the literal W* above and
transports the normality, elementary structure, orders and commutators.

Source: Stellmacher (10.1)(a3), printed p.61, the first W* paragraph in
`refs/files/stellmacher-n-group.pdf`. The subsequent ambient normalizer
identities and involution-fusion contradiction are separate results.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_small_centralizer_elementary
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    let W0 := NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓
      GeneratedNeighborhoodV ctx.Γ middle
    let Wstar := QAt ctx.Γ middle ⊓ Subgroup.centralizer (W0 : Set G)
    GAt ctx.Γ middle ≤ Subgroup.normalizer (Wstar : Set G) ∧
      IsElementaryAbelian 2 Wstar ∧ (Nat.card Wstar = 8 ∨ Nat.card Wstar = 16) ∧
      Wstar ⊓ twoCoreIn (EAt ctx.Γ middle) = ZAt ctx.Γ middle ∧
      ⁅Wstar,EAt ctx.Γ middle⁆ ≤ ZAt ctx.Γ middle := by
  let M := GAt ctx.Γ middle
  let E := twoResidualAmbient (⊤ : Subgroup M)
  let Q := pCore 2 M
  let R := E ⊓ Q
  let D := twoCoreIn (EAt ctx.Γ middle)
  let K := NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle)
  let W := GeneratedNeighborhoodV ctx.Γ middle
  let W0 := K ⊓ W
  let U := W0.subgroupOf M
  let Z := (ZAt ctx.Γ middle).subgroupOf M
  let C := Q ⊓ Subgroup.centralizer (U : Set M)
  let Wstar := QAt ctx.Γ middle ⊓ Subgroup.centralizer (W0 : Set G)
  let _ : E.Normal := by
    dsimp only [E]
    rw [SectionThree.twoResidualAmbient_top_eq_hktPResidual]
    exact BenderSuzuki.External.hktPResidual_normal
  obtain ⟨hcenter,hc4,himage⟩ := ten_one_small_middle_bound_inputs ctx middle hpath hsmall hmodel
  have hEmap : E.map M.subtype = EAt ctx.Γ middle := by
    have hm := map_twoResidualAmbient_of_subgroup_image (⊤ : Subgroup M) M.subtype M
      (by rw [← MonoidHom.range_eq_map,Subgroup.range_subtype])
    exact hm.trans (ctx.Γ.twoResidualAt_def middle).symm
  have hQmap : Q.map M.subtype = QAt ctx.Γ middle :=
    (ctx.Γ.twoCoreAt_def middle).symm
  have hRmap : R.map M.subtype = D := by
    rw [Subgroup.map_inf E Q M.subtype M.subtype_injective,hEmap,hQmap]
    change ctx.Γ.twoResidualAt middle ⊓ ctx.Γ.twoCoreAt middle =
      twoCoreIn (ctx.Γ.twoResidualAt middle)
    rw [ctx.Γ.twoResidualAt_def,ctx.Γ.twoCoreAt_def,residual_core_eq_inter_core]
  have hZmiddleQ : ZAt ctx.Γ middle ≤ QAt ctx.Γ middle := by
    rw [(sectionTenOpeningData ctx middle hpath).center_omega]
    exact Subgroup.map_subtype_le _
  have hQmiddleM : QAt ctx.Γ middle ≤ M := hQmap ▸ Subgroup.map_subtype_le Q
  have hZmiddleM : ZAt ctx.Γ middle ≤ M := hZmiddleQ.trans hQmiddleM
  have hZmap : Z.map M.subtype = ZAt ctx.Γ middle :=
    Subgroup.map_subgroupOf_eq_of_le hZmiddleM
  have hZR : Z ≤ R := by
    intro z hz
    have hh := ten_one_middle_center_le_residual_core ctx middle hpath hz
    change (z:G) ∈ D at hh
    rw [← hRmap] at hh
    obtain ⟨r,hr,heq⟩ := hh
    exact (M.subtype_injective heq) ▸ hr
  have hZcentral : Z ≤ Subgroup.centralizer (Q : Set M) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    apply Subtype.ext
    have hZcent : ZAt ctx.Γ middle ≤ Subgroup.centralizer (QAt ctx.Γ middle : Set G) := by
      rw [(sectionTenOpeningData ctx middle hpath).center_omega]
      exact (omegaOneCenter_le_centerAmbient _).trans (centerAmbient_le_centralizer _)
    exact Subgroup.mem_centralizer_iff.mp (hZcent hz) q
      (hQmap ▸ Subgroup.mem_map_of_mem M.subtype hq)
  have hZcard : Nat.card Z = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZmiddleM).toEquiv]
    exact (sectionTenOpeningData ctx middle hpath).center_card
  obtain ⟨hMW0,hUel,hW0card⟩ := ten_one_small_common_core_elementary ctx middle hpath hsmall hmodel
  change M ≤ Subgroup.normalizer (W0 : Set G) at hMW0
  let _ : IsElementaryAbelian 2 W0 := hUel
  have hW0Q : W0 ≤ QAt ctx.Γ middle :=
    inf_le_right.trans (nine_seven_neighborhood_le_own_core
      ctx.toLocalContext.toSectionNineLocalContext
        (by change 2 < ctx.criticalPath.length; rw [ctx.critical_length]; decide) middle)
  have hW0M : W0 ≤ M := hW0Q.trans hQmiddleM
  let _ : U.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hW0M).mpr hMW0
  let _ : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hW0M
  have hUcard : Nat.card U = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW0M).toEquiv]
    exact hW0card
  have hUQ : U ≤ Q := by
    intro u hu
    have hh := hW0Q hu
    rw [← hQmap] at hh
    obtain ⟨q,hq,heq⟩ := hh
    exact (M.subtype_injective heq) ▸ hq
  have hZU : Z ≤ U := by
    intro z hz
    constructor
    · change (z:G) ∈ sInf {D : Subgroup G | ∃ neighbor,
        neighbor ∈ Neighborhood ctx.Γ middle ∧ D = QAt ctx.Γ neighbor}
      rw [Subgroup.mem_sInf]
      rintro D ⟨neighbor,hneighbor,rfl⟩
      exact ((nine_seven_neighbor_center_le_module ctx.Γ
        (ctx.Γ.adjacent_symm ((mem_neighborhood_iff_adjacent ctx.Γ).mp hneighbor))).trans
          (neighbor_join_le_core_of_length_gt_one ctx.Γ ctx.criticalPath
            (by rw [ctx.critical_length]; decide) neighbor)) hz
    · obtain ⟨_,hfirst,_,_⟩ := sectionTenOpeningGeometry ctx middle hpath
      have hZW : ZAt ctx.Γ middle ≤ W :=
        (nine_seven_neighbor_center_le_module ctx.Γ (ctx.Γ.adjacent_symm hfirst)).trans
          (show VAt ctx.Γ ctx.criticalPath.firstStep ≤ W from
            le_sSup ⟨_,(mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst,rfl⟩)
      exact hZW hz
  have hCmap : C.map M.subtype = Wstar := by
    apply le_antisymm
    · rintro _ ⟨c,hc,rfl⟩
      refine ⟨hQmap ▸ Subgroup.mem_map_of_mem M.subtype hc.1,?_⟩
      change (c:G) ∈ Subgroup.centralizer (W0 : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact congrArg Subtype.val
        (Subgroup.mem_centralizer_iff.mp hc.2 ⟨w,hW0M hw⟩ hw)
    · intro c hc
      have hh : c ∈ Q.map M.subtype := hQmap ▸ hc.1
      obtain ⟨q,hq,heq⟩ := hh
      refine ⟨q,⟨hq,?_⟩,heq⟩
      change q ∈ Subgroup.centralizer (U : Set M)
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      apply Subtype.ext
      change (w:G)*(q:G)=(q:G)*(w:G)
      change (q:G)=c at heq
      rw [heq]
      exact Subgroup.mem_centralizer_iff.mp hc.2 w hw
  obtain ⟨hel,hCcard,hCR,hCE⟩ :=
    Subgroup.elementary_centralizer_of_centerfree_c4_square_residual
      (default : Sylow 2 M) E Q U Z (twoResidualAmbient_top_sup_sylow _)
      (pCore_isPGroup (p:=2) (G:=M)) hcenter hc4 himage hUQ hUcard hZR hZU hZcard hZcentral
  let _ : IsElementaryAbelian 2 C := hel
  have hnorm : M ≤ Subgroup.normalizer (Wstar : Set G) := by
    rw [← hCmap]
    have hh := C.le_normalizer_map M.subtype
    rw [Subgroup.normalizer_eq_top,← MonoidHom.range_eq_map,Subgroup.range_subtype] at hh
    exact hh
  refine ⟨hnorm,?_,?_,?_,?_⟩
  · change IsElementaryAbelian 2 Wstar
    rw [← hCmap]
    exact IsElementaryAbelian.map _
  · change Nat.card Wstar = 8 ∨ Nat.card Wstar = 16
    rw [← hCmap,Subgroup.card_map_of_injective M.subtype_injective]
    exact hCcard
  · have hh := congrArg (Subgroup.map M.subtype) hCR
    rw [Subgroup.map_inf _ _ _ M.subtype_injective,hCmap,hRmap,hZmap] at hh
    exact hh
  · have hh := Subgroup.map_mono (f:=M.subtype) hCE
    rw [Subgroup.map_commutator,hCmap,hEmap,hZmap] at hh
    exact hh

end Stellmacher.SectionTen
