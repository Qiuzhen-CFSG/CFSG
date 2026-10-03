module
public import Stellmacher.SectionTen.TenOneSmallCentralizerElementary
public import Stellmacher.SectionTen.TenOneSmallMiddleCoreClassTwo
public import Theory.GroupTheory.CentralCommutatorEightCenter

/-!
# The full center and elementary quotient of the small middle core

Under the actual order-eight first-module and SL₂(2) quotient hypotheses,
the full center of Qmiddle is Zmiddle. Consequently the literal quotient
Qmiddle/Zmiddle is elementary abelian; its normality witness is explicit.

Inside the middle stabilizer the abelian residual-core intersection is
self-centralizing in its two-core, by the center-free odd-residual theorem.
Subtype transport gives the same self-centralizer equation for O₂(Emiddle)
in Qmiddle. The full center of Qmiddle therefore lies in that residual core,
and also in W*=C_Qmiddle(W₀). The proved intersection W*∩O₂(Emiddle)=Zmiddle
identifies the full center. Finally, the class-two result puts commutators
in the elementary central four-subgroup. Their exponent two makes every
square central, so every square lies in Zmiddle and the quotient is elementary.

Source: Stellmacher (10.1)(a3), printed p.61 of
`refs/files/stellmacher-n-group.pdf`. These give the elementary quotient
used by the following ambient normalizer argument, for both W* orders.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

private theorem selfcentralizing_residual_core
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    QAt ctx.Γ middle ⊓ Subgroup.centralizer (twoCoreIn (EAt ctx.Γ middle) : Set G) =
      twoCoreIn (EAt ctx.Γ middle) := by
  let M := GAt ctx.Γ middle
  let E := twoResidualAmbient (⊤ : Subgroup M)
  let Q := pCore 2 M
  let R := E ⊓ Q
  let D := twoCoreIn (EAt ctx.Γ middle)
  let _ : E.Normal := by
    dsimp only [E]
    rw [SectionThree.twoResidualAmbient_top_eq_hktPResidual]
    exact BenderSuzuki.External.hktPResidual_normal
  obtain ⟨hcenter,hc4,himage⟩ := ten_one_small_middle_bound_inputs ctx middle hpath hsmall hmodel
  obtain ⟨equiv⟩ := hc4
  let _ : CommGroup R := equiv.toMonoidHom.commGroupOfInjective equiv.injective
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
  have hK : Q ⊓ Subgroup.centralizer (R : Set M) = R :=
    inf_centralizer_inf_eq_of_centerfree_odd_image (default : Sylow 2 M) E Q
      (twoResidualAmbient_top_sup_sylow _) (pCore_isPGroup (p:=2) (G:=M))
      hcenter (by rw [himage]; decide)
  change QAt ctx.Γ middle ⊓ Subgroup.centralizer (D : Set G) = D
  apply le_antisymm
  · intro x hx
    have hxQ : x ∈ Q.map M.subtype := hQmap ▸ hx.1
    obtain ⟨q,hq,heq⟩ := hxQ
    have hqC : q ∈ Subgroup.centralizer (R : Set M) := by
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      apply Subtype.ext
      change (r:G)*(q:G)=(q:G)*(r:G)
      change (q:G)=x at heq
      rw [heq]
      exact Subgroup.mem_centralizer_iff.mp hx.2 r
        (hRmap ▸ Subgroup.mem_map_of_mem M.subtype hr)
    have hqR : q ∈ R := hK ▸ (show q ∈ Q ⊓ Subgroup.centralizer (R : Set M) from ⟨hq,hqC⟩)
    rw [← hRmap]
    exact ⟨q,hqR,heq⟩
  · have hRD : D ≤ QAt ctx.Γ middle := by
      rw [← hRmap,← hQmap]
      exact Subgroup.map_mono inf_le_right
    have hcomm : IsMulCommutative D := by
      rw [← hRmap]
      infer_instance
    let _ := hcomm
    exact le_inf hRD (Subgroup.le_centralizer D)

public theorem ten_one_small_middle_core_center
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    CenterAmbient (QAt ctx.Γ middle) = ZAt ctx.Γ middle := by
  let Q := QAt ctx.Γ middle
  let D := twoCoreIn (EAt ctx.Γ middle)
  let W0 := NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓
    GeneratedNeighborhoodV ctx.Γ middle
  let Wstar := Q ⊓ Subgroup.centralizer (W0 : Set G)
  have hZQ : ZAt ctx.Γ middle ≤ Q := by
    rw [(sectionTenOpeningData ctx middle hpath).center_omega]
    exact Subgroup.map_subtype_le _
  have hcent : CenterAmbient Q ≤ Q := Subgroup.map_subtype_le _
  have hcentC : CenterAmbient Q ≤ Subgroup.centralizer (Q : Set G) :=
    centerAmbient_le_centralizer Q
  have hW0Q : W0 ≤ Q := inf_le_right.trans
    (nine_seven_neighborhood_le_own_core ctx.toLocalContext.toSectionNineLocalContext
      (by change 2 < ctx.criticalPath.length; rw [ctx.critical_length]; decide) middle)
  have hDQ : D ≤ Q := by
    change twoCoreIn (ctx.Γ.twoResidualAt middle) ≤ ctx.Γ.twoCoreAt middle
    rw [ctx.Γ.twoResidualAt_def,ctx.Γ.twoCoreAt_def,residual_core_eq_inter_core]
    exact inf_le_right
  have hcentW : CenterAmbient Q ≤ Wstar := le_inf hcent
    (hcentC.trans (Subgroup.centralizer_le hW0Q))
  have hcentD : CenterAmbient Q ≤ D := by
    change CenterAmbient Q ≤ twoCoreIn (EAt ctx.Γ middle)
    rw [← selfcentralizing_residual_core ctx middle hpath hsmall hmodel]
    exact le_inf hcent (hcentC.trans (Subgroup.centralizer_le hDQ))
  have hWstarD : Wstar ⊓ D = ZAt ctx.Γ middle :=
    (ten_one_small_centralizer_elementary ctx middle hpath hsmall hmodel).2.2.2.1
  apply le_antisymm
  · rw [← hWstarD]
    exact le_inf hcentW hcentD
  · rw [(sectionTenOpeningData ctx middle hpath).center_omega]
    exact omegaOneCenter_le_centerAmbient Q

public theorem ten_one_small_middle_core_quotient_elementary
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    ∃ hN : ((ZAt ctx.Γ middle).subgroupOf (QAt ctx.Γ middle)).Normal,
      let _ := hN
      IsElementaryAbelian 2 (QAt ctx.Γ middle ⧸
        (ZAt ctx.Γ middle).subgroupOf (QAt ctx.Γ middle)) := by
  let Q := QAt ctx.Γ middle
  let Z := ZAt ctx.Γ middle
  have hcenter : Subgroup.center Q = Z.subgroupOf Q := by
    have hh := congrArg (Subgroup.comap Q.subtype)
      (ten_one_small_middle_core_center ctx middle hpath hsmall hmodel)
    change ((Subgroup.center Q).map Q.subtype).comap Q.subtype = Z.subgroupOf Q at hh
    rw [Subgroup.comap_map_eq_self_of_injective Q.subtype_injective] at hh
    exact hh
  have hN : (Z.subgroupOf Q).Normal := hcenter ▸ inferInstance
  let _ := hN
  have hZQ : Z ≤ Q := by
    rw [show Z = omegaOneCenter Q from (sectionTenOpeningData ctx middle hpath).center_omega]
    exact Subgroup.map_subtype_le _
  let _ : IsElementaryAbelian 2 Z := by
    rw [show Z = omegaOneCenter Q from (sectionTenOpeningData ctx middle hpath).center_omega]
    exact omegaOneCenterAmbient_elementaryAbelian _
  let _ : IsElementaryAbelian 2 (Z.subgroupOf Q) := IsElementaryAbelian.subgroupOf hZQ
  have hcomm : commutator Q ≤ Z.subgroupOf Q := by
    intro q hq
    apply ten_one_small_middle_core_commutator_le_center ctx middle hpath hsmall hmodel
    rw [← Subgroup.map_subtype_commutator Q]
    exact Subgroup.mem_map_of_mem Q.subtype hq
  have hsquare (q : Q) : q^2 ∈ Z.subgroupOf Q := by
    rw [← hcenter]
    exact Subgroup.square_mem_center_of_elementary_central_commutator
      (Z.subgroupOf Q) inferInstance (le_inf hcomm (hcenter ▸ hcomm)) q
  have hquotcomm : IsMulCommutative (Q ⧸ Z.subgroupOf Q) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcomm
  let _ := hquotcomm
  refine ⟨hN,⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_⟩⟩
  intro x
  obtain ⟨q,rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf Q) x
  rw [← map_pow]
  exact (QuotientGroup.eq_one_iff (q^2)).mpr (hsquare q)

end Stellmacher.SectionTen
