module

public import Stellmacher.SectionNine.NineSevenResidualTwoArc
public import Stellmacher.SectionEight.GeneratedEightSixSL2ResidualOdd
public import Stellmacher.SectionOne.SL2DerivedInvolutionGenerate
public import Stellmacher.TwoResidualIdentification

/-!
# Residual-commutator neighbor transport for (9.6)

Suppose the first core quotient in the genuine local Section Nine graph is
SL₂(2). For any involutory element of its stabilizer outside the core, the
commutator of its cyclic subgroup with the first residual is transitive on
the neighbors of the first step.

The residual maps onto the derived subgroup of SL₂(2), of order three. The
commutator of that subgroup with a nontrivial involution is the whole derived
subgroup: otherwise the involution would centralize both generators of the
order-six group and contradict its trivial center. A residual neighbor
transporter therefore has the same quotient image as an element of the
specified commutator. Their difference lies in the two-core and fixes every
neighbor, giving the required literal commutator transporter.

This supplies the conjugator used in the applications of (9.4) in the proof
of Stellmacher (9.6), printed p.53 / PDF p.43 of
`refs/files/stellmacher-n-group.pdf`. It asserts transitivity on immediate
neighbors only; the image of the third path vertex then determines the
backward neighbor needed by the application.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionEight
universe u

private theorem sl2_residual_commutator
    {M : Type*} [Group M] [Finite M] (hM : IsSL2Two M)
    (t : M) (hne : t ≠ 1) (hsquare : t ^ 2 = 1) :
    ⁅commutator M, Subgroup.zpowers t⁆ = commutator M := by
  have hcard := SectionOne.RankOneThreeGroupAssembly.isSL2Two_card hM
  have hderived := isSL2Two_commutator_card hM
  have htwo : Nat.card (Subgroup.zpowers t) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hsquare hne]
  have hgen : commutator M ⊔ Subgroup.zpowers t = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    have hthreeDvd : 3 ∣ Nat.card (commutator M ⊔ Subgroup.zpowers t : Subgroup M) :=
      hderived ▸ Subgroup.card_dvd_of_le
        (le_sup_left : commutator M ≤ commutator M ⊔ Subgroup.zpowers t)
    have htwoDvd : 2 ∣ Nat.card (commutator M ⊔ Subgroup.zpowers t : Subgroup M) :=
      htwo ▸ Subgroup.card_dvd_of_le
        (le_sup_right : Subgroup.zpowers t ≤ commutator M ⊔ Subgroup.zpowers t)
    have hsixDvd : 6 ∣ Nat.card (commutator M ⊔ Subgroup.zpowers t : Subgroup M) :=
      (show Nat.Coprime 3 2 by decide).mul_dvd_of_dvd_of_dvd hthreeDvd htwoDvd
    apply le_antisymm (Nat.card_le_card_of_injective _ (Subgroup.subtype_injective _))
    rw [hcard]
    exact Nat.le_of_dvd Nat.card_pos hsixDvd
  have hnot : ⁅commutator M, Subgroup.zpowers t⁆ ≠ ⊥ := by
    intro hbot
    have hderivedCentral := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
    have hcyclicCentral : Subgroup.zpowers t ≤
        Subgroup.centralizer (Subgroup.zpowers t : Set M) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (Subgroup.commutator_self_eq_bot_iff.mpr inferInstance)
    have hcentral := sup_le hderivedCentral hcyclicCentral
    rw [hgen] at hcentral
    have htcenter : t ∈ Subgroup.center M := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact (Subgroup.mem_centralizer_iff.mp (hcentral (Subgroup.mem_top g))
        t (Subgroup.mem_zpowers t)).symm
    rw [SectionOne.RankOneThreeGroupAssembly.center_eq_bot_of_isSL2Two hM,
      Subgroup.mem_bot] at htcenter
    exact hne htcenter
  have hle : ⁅commutator M, Subgroup.zpowers t⁆ ≤ commutator M :=
    Subgroup.commutator_le_left _ _
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [hderived] at hdvd
  have hcommCard : Nat.card (⁅commutator M, Subgroup.zpowers t⁆ : Subgroup M) = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with hone | hthree
    · exact (hnot (Subgroup.card_eq_one.mp hone)).elim
    · exact hthree
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hderived,hcommCard])

public theorem nine_six_residual_commutator_neighbor_transitive
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (t : G) (ht : t ∈ GAt ctx.Γ ctx.criticalPath.firstStep)
    (houtside : t ∉ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hsquare : t ^ 2 = 1)
    (left right : ctx.Γ.Vertex)
    (hleft : ctx.Γ.adjacent ctx.criticalPath.firstStep left)
    (hright : ctx.Γ.adjacent ctx.criticalPath.firstStep right) :
    ∃ x : G, x ∈ ⁅EAt ctx.Γ ctx.criticalPath.firstStep, Subgroup.zpowers t⁆ ∧
      ctx.Γ.act x left = right := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let E := EAt Γ cp.firstStep
  let Q := QAt Γ cp.firstStep
  let tP : P := ⟨t,ht⟩
  let D := ⁅E,Subgroup.zpowers t⁆
  obtain ⟨projection,hsurj,hker⟩ := hquot
  have htne : projection tP ≠ 1 := by
    intro heq
    have hmem : tP ∈ projection.ker := MonoidHom.mem_ker.mpr heq
    rw [hker] at hmem
    exact houtside hmem
  have ht2 : (projection tP)^2=1 := by
    rw [← map_pow,show tP^2=1 from Subtype.ext hsquare,map_one]
  have hEP : E ≤ P := by
    change Γ.twoResidualAt cp.firstStep ≤ Γ.vertexStabilizer cp.firstStep
    rw [Γ.twoResidualAt_def]
    exact twoResidualIn_le _
  have htP : Subgroup.zpowers t ≤ P := Subgroup.zpowers_le.mpr ht
  have hDP : D ≤ P := (Subgroup.commutator_le_sup _ _).trans (sup_le hEP htP)
  have hnative : E.subgroupOf P = twoResidualAmbient (⊤ : Subgroup P) := by
    change (Γ.twoResidualAt cp.firstStep).subgroupOf P = _
    rw [Γ.twoResidualAt_def]
    change ((twoResidualSubgroup P).map P.subtype).subgroupOf P = _
    rw [subgroupOf_map_subtype_eq, SectionThree.twoResidualSubgroup_eq_hktPResidual',
      SectionThree.twoResidualAmbient_top_eq_hktPResidual]
  have hEmap : (E.subgroupOf P).map projection = commutator SL2Two := by
    rw [hnative,map_twoResidualAmbient_of_subgroup_image ⊤ projection ⊤
      (Subgroup.map_top_of_surjective projection hsurj),
      eight_six_sl2_residual_eq_commutator]
  have hDnative : D.subgroupOf P =
      ⁅E.subgroupOf P,Subgroup.zpowers tP⁆ := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hDP,Subgroup.map_commutator,
      Subgroup.map_subgroupOf_eq_of_le hEP,MonoidHom.map_zpowers]
    rfl
  have hDmap : (D.subgroupOf P).map projection = commutator SL2Two := by
    rw [hDnative,Subgroup.map_commutator,hEmap,MonoidHom.map_zpowers]
    exact sl2_residual_commutator ⟨MulEquiv.refl _⟩ (projection tP) htne ht2
  obtain ⟨mover,hmover,hmove⟩ := nine_seven_residual_neighbor_transitive
    ctx.sectionSeven Γ cp.firstStep left right hleft hright
  let moverP : P := ⟨mover,hEP hmover⟩
  have himage : projection moverP ∈ (D.subgroupOf P).map projection := by
    rw [hDmap,← hEmap]
    exact Subgroup.mem_map_of_mem projection (show moverP ∈ E.subgroupOf P from hmover)
  obtain ⟨chosen,hchosen,heq⟩ := himage
  have herror : chosen*moverP⁻¹ ∈ projection.ker := by
    rw [MonoidHom.mem_ker,map_mul,map_inv,heq,mul_inv_cancel]
  rw [hker] at herror
  have herrorQ : (chosen:G)*mover⁻¹ ∈ Q := herror
  have hfix := (cubic_local_action_of_sl2Two_quotient Γ ctx.sectionSeven
    cp.firstStep ⟨projection,hsurj,hker⟩).kernel
      ⟨(chosen:G)*mover⁻¹,P.mul_mem chosen.property (P.inv_mem moverP.property)⟩
  have hfixed : Γ.act ((chosen:G)*mover⁻¹) left = left :=
    hfix.mp herrorQ left hleft
  have hcancel := congrArg (Γ.act mover) hfixed
  rw [← Γ.act_mul] at hcancel
  simp only [mul_assoc,inv_mul_cancel,mul_one] at hcancel
  exact ⟨chosen,hchosen,hcancel.trans hmove⟩

end Stellmacher.SectionNine
