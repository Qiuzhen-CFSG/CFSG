module
public import Stellmacher.SectionTen.TenOneMiddleCenterResidual
public import Stellmacher.SectionNine.NineSevenResidualTwoArc
public import Stellmacher.SectionNine.NineSevenNormalityObstructions
public import Theory.GroupAction.SubgroupQuotientFullAction
public import Theory.GroupTheory.SpecificGroups.PermThreeNormalKernel
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree

/-!
# The middle residual action on the neighborhood omega center

In the actual Section Ten geometry, suppose the terminal residual two-core
moves the middle neighborhood omega center only inside the terminal center
line. Then the middle two-residual moves that omega center exactly by the
middle four-center. This transfer needs no choice of a fixed component,
no no-transvection premise beyond the supplied commutator bound, and no
source-(16) or final local-model conclusion.

The middle center lies in the neighborhood omega center. Construct the literal
conjugation action on the quotient by that center. Its kernel contains the
terminal residual two-core, a two-group escaping the middle core. The proved
S3 normal-kernel theorem makes the action quotient a two-group, so the middle
two-residual lies in its kernel. This gives the commutator upper bound.
The known full residual action on the middle center gives the reverse bound.

Source: Stellmacher, (10.1), Journal of Algebra 190 (1997), printed p.64,
the last paragraph before (16). This supplies the affine four-point action
used by the following local-centralizer transitivity contradiction.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
open scoped commutatorElement
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

omit [Finite G] in
private theorem normalizes_omega (Q : Subgroup G) :
    Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (omegaOneCenter Q : Set G) := by
  let K : Subgroup Q := (omega₁ (G := Subgroup.center Q) (p := 2)).map (Subgroup.center Q).subtype
  let _ : (omega₁ (G := Subgroup.center Q) (p := 2)).Characteristic := omega₁_characteristic (Subgroup.center Q)
  let _ : K.Characteristic := inferInstance
  exact BenderSuzuki.External.hkt_normalizer_le_normalizer_map_subtype_of_characteristic Q K

public theorem ten_one_omega_middle_residual_commutator
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hcomm : ⁅omegaOneCenter (GeneratedNeighborhoodV ctx.Γ middle),
      twoCoreIn (EAt ctx.Γ ctx.criticalPath.a')⁆ ≤ ZAt ctx.Γ ctx.criticalPath.a') :
    ⁅omegaOneCenter (GeneratedNeighborhoodV ctx.Γ middle), EAt ctx.Γ middle⁆ =
      ZAt ctx.Γ middle := by
  let P := GAt ctx.Γ middle
  let Q := QAt ctx.Γ middle
  let E := EAt ctx.Γ middle
  let Z := ZAt ctx.Γ middle
  let W := GeneratedNeighborhoodV ctx.Γ middle
  let O := omegaOneCenter W
  let U := twoCoreIn (EAt ctx.Γ ctx.criticalPath.a')
  obtain ⟨_,_hfirst,hterminal,_⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hlong : 2 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  have hWQ : W ≤ Q := nine_seven_neighborhood_le_own_core
    ctx.toLocalContext.toSectionNineLocalContext hlong middle
  have hQP : Q ≤ P := by
    change ctx.Γ.twoCoreAt middle ≤ P
    rw [ctx.Γ.twoCoreAt_def]
    exact twoCoreIn_le P
  have hOW : O ≤ W := (omegaOneCenter_le_centerAmbient W).trans (Subgroup.map_subtype_le _)
  have hOP : O ≤ P := hOW.trans (hWQ.trans hQP)
  have hPZ : P ≤ Subgroup.normalizer (Z : Set G) := stabilizer_le_normalizer_z ctx.Γ middle
  have hPO : P ≤ Subgroup.normalizer (O : Set G) :=
    (nine_seven_stabilizer_normalizes_neighborhood ctx.Γ middle).trans (normalizes_omega W)
  have hZW : Z ≤ W :=
    (nine_seven_neighbor_center_le_module ctx.Γ (ctx.Γ.adjacent_symm hterminal)).trans
      (le_sSup ⟨_,(mem_neighborhood_iff_adjacent ctx.Γ).mpr hterminal,rfl⟩)
  have hZQcenter : Z ≤ CenterAmbient Q := by
    change ZAt ctx.Γ middle ≤ CenterAmbient Q
    rw [(sectionTenOpeningData ctx middle hpath).center_omega]
    exact omegaOneCenter_le_centerAmbient Q
  have hZtwo : IsElementaryAbelian 2 Z := by
    change IsElementaryAbelian 2 (ZAt ctx.Γ middle)
    rw [(sectionTenOpeningData ctx middle hpath).center_omega]
    exact omegaOneCenterAmbient_elementaryAbelian Q
  let _ := hZtwo
  have hZO : Z ≤ O := by
    intro x hx
    exact (mem_omegaOneCenterAmbient_iff W x).mpr
      ⟨hZW hx,elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx,
        Subgroup.mem_centralizer_iff.mp
          (((hZQcenter.trans (centerAmbient_le_centralizer Q)).trans
            (Subgroup.centralizer_le hWQ)) hx)⟩
  have hZnext : ZAt ctx.Γ ctx.criticalPath.a' ≤ Z := by
    change ZAt ctx.Γ ctx.criticalPath.a' ≤ ZAt ctx.Γ middle
    rw [(sectionTenOpeningData ctx middle hpath).center_direct_product.1]
    exact le_sup_right
  have hN : (Z.subgroupOf O).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hOP.trans hPZ)
  let _ := hN
  obtain ⟨action,hformula⟩ := Subgroup.exists_quotient_conjugation_action P O Z hPO hPZ hN
  have hUK : U.subgroupOf P ≤ action.ker :=
    Subgroup.quotient_conjugation_action_kills_commutator_layer P O Z U hN hPO
      (hcomm.trans hZnext) action hformula
  have hUQnext : U ≤ QAt ctx.Γ ctx.criticalPath.a' := by
    change twoCoreIn (ctx.Γ.twoResidualAt ctx.criticalPath.a') ≤ ctx.Γ.twoCoreAt ctx.criticalPath.a'
    rw [ctx.Γ.twoResidualAt_def,ctx.Γ.twoCoreAt_def,residual_core_eq_inter_core]
    exact inf_le_right
  have hUP : U ≤ P := hUQnext.trans
    (((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core _ _
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (ctx.Γ.adjacent_symm hterminal)) default).2.2)
  obtain ⟨alignment,_,halign⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq
  have hUnot : ¬ U ≤ Q := nine_seven_residual_core_escapes_neighbor
    ctx.toLocalContext.toSectionNineLocalContext ctx.criticalPath.a' middle
      ⟨alignment,halign⟩ (ctx.Γ.adjacent_symm hterminal)
  have hUtwo : IsPGroup 2 U := (pCore_isPGroup (p := 2) (G := EAt ctx.Γ ctx.criticalPath.a')).map _
  have hQtwo : IsPGroup 2 (Q.subgroupOf P) := by
    have hQ : Q = twoCoreIn P := ctx.Γ.twoCoreAt_def middle
    rw [hQ,twoCoreIn,Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective P.subtype_injective]
    exact pCore_isPGroup
  obtain ⟨projection,hsurj,hker⟩ := (sectionTenOpeningData ctx middle hpath).quotient_model
  obtain ⟨equiv⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  let f := equiv.toMonoidHom.comp projection
  have hquot : IsPGroup 2 (P ⧸ action.ker) :=
    Subgroup.quotient_isPGroup_two_of_perm_three_normal_kernel
      (Q.subgroupOf P) action.ker (U.subgroupOf P) hQtwo f
      (equiv.surjective.comp hsurj)
      (by dsimp only [f]; rw [MonoidHom.ker_comp_of_injective _ _ equiv.injective]; exact hker)
      (hUtwo.of_equiv (Subgroup.subgroupOfEquivOfLe hUP).symm) hUK (by
        intro hle
        apply hUnot
        intro x hx
        exact hle (show (⟨x,hUP hx⟩ : P) ∈ U.subgroupOf P from hx))
  have hres : twoResidualSubgroup P ≤ action.ker := by
    rw [SectionThree.twoResidualSubgroup_eq_hktPResidual']
    exact BenderSuzuki.External.hktPResidual_le action.ker inferInstance hquot
  have hEK : E ≤ action.ker.map P.subtype := by
    have hE : E = twoResidualIn P := ctx.Γ.twoResidualAt_def middle
    rw [hE,twoResidualIn,twoResidualAmbient]
    exact Subgroup.map_mono hres
  apply le_antisymm
  · rw [Subgroup.commutator_comm]
    apply Subgroup.commutator_le.mpr
    intro actor hactor point hpoint
    obtain ⟨a,ha,rfl⟩ := hEK hactor
    have hfix : action a (QuotientGroup.mk' (Z.subgroupOf O) (⟨point,hpoint⟩ : O)) =
        QuotientGroup.mk' (Z.subgroupOf O) (⟨point,hpoint⟩ : O) := by
      rw [show action a = 1 from ha]
      rfl
    rw [hformula] at hfix
    have hmem := QuotientGroup.eq_iff_div_mem.mp hfix
    change (a : G)*point*(a : G)⁻¹/point ∈ Z at hmem
    change ⁅(a : G),point⁆ ∈ Z
    simpa only [commutatorElement_def,div_eq_mul_inv] using hmem
  · rw [← ten_one_middle_center_full_residual ctx middle hpath]
    exact Subgroup.commutator_mono hZO le_rfl

end Stellmacher.SectionTen
