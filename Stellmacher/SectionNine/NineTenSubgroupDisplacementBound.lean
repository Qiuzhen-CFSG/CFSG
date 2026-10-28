module

public import Stellmacher.SectionNine.NineTenSelectedSupport
public import Stellmacher.SectionNine.NineTenPredecessorTerminalTransfer
public import Stellmacher.SectionOne.OneSevenCommutingInvolutionSupport
public import Theory.GroupAction.SubgroupQuotientCommutatorBound
public import Theory.GroupAction.ActorSubtypeCommutator

/-!
# A subgroup displacement bound with the retained canonical support

A subgroup centralizing the initial center, lying in the terminal stabilizer
and centralizing the penultimate center has neighbor-center displacement in
R joined with the terminal center. The supplied initial-center actor, literal
quotient action, and canonical support are retained. The subgroup itself may
be a proper intersection of the predecessor module with a stabilizer.

Initial-center centralization makes each subgroup element commute with
the selected actor. In the literal faithful quotient action, the canonical
factor's commuting-involution support calculation bounds displacement by the
actor's line. The penultimate-center image is fixed, so the support containment
extends this bound to the retained neighbor center. Quotient lifting gives the
ambient commutator bound, and (7.4) puts R in the first module.

This is the support argument of Stellmacher (9.10), printed pp.57–58,
applied after (7) to the predecessor/penultimate-stabilizer intersection and
in (9) to the chosen neighbor group. The original one-step-neighborhood
interface remains a wrapper using abelianness of that join.
-/

open scoped IsMulCommutative

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

universe u

public theorem nine_ten_subgroup_displacement_bound_of_initial_center_centralization
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 4 < ctx.criticalPath.length)
    (K : Subgroup G)
    (hKinitial : K ≤ Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set G))
    (hKP : K ≤ GAt ctx.Γ ctx.criticalPath.a')
    (neighbor : ctx.Γ.Vertex)
    (hneighbor : neighbor ∈ neighborhood ctx.Γ ctx.criticalPath.a')
    (hmodules : ⁅K,
      ZAt ctx.Γ (ctx.criticalPath.path
        ⟨ctx.criticalPath.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)⁆ = ⊥)
    (selected : GAt ctx.Γ ctx.criticalPath.a')
    (hselected : (selected : G) ∈ ZAt ctx.Γ ctx.criticalPath.a)
    (hselectedNot : (selected : G) ∉ QAt ctx.Γ ctx.criticalPath.a')
    [hN : ((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a')).Normal]
    [hW : IsElementaryAbelian 2 (VAt ctx.Γ ctx.criticalPath.a' ⧸
      (ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a'))]
    (action : GAt ctx.Γ ctx.criticalPath.a' →* MulAut
      (VAt ctx.Γ ctx.criticalPath.a' ⧸
        (ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a')))
    (hformula : ∀ mover : GAt ctx.Γ ctx.criticalPath.a', ∀ point : VAt ctx.Γ ctx.criticalPath.a',
      action mover (QuotientGroup.mk'
        ((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a')) point) =
        QuotientGroup.mk'
          ((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a'))
          ⟨(mover : G) * (point : G) * (mover : G)⁻¹,
            (Subgroup.mem_normalizer_iff.mp
              (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.a' mover.property)
                point).mp point.property⟩)
    (hkernel : action.ker = pCore 2 (GAt ctx.Γ ctx.criticalPath.a'))
    (hyp : SectionOne.Hypotheses action.range (VAt ctx.Γ ctx.criticalPath.a' ⧸
      (ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a')))
    (D : Subgroup action.range)
    (hD : SectionOne.IsOneSevenFactor
      (V := VAt ctx.Γ ctx.criticalPath.a' ⧸
        (ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a')) D)
    (hselectedD : action.rangeRestrict selected ∈ D)
    (hsupport :
      ((ZAt ctx.Γ neighbor).subgroupOf (VAt ctx.Γ ctx.criticalPath.a')).map
          (QuotientGroup.mk'
            ((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a'))) ≤
        commutatorAction D (VAt ctx.Γ ctx.criticalPath.a' ⧸
          (ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a')) ⊔
          ((ZAt ctx.Γ (ctx.criticalPath.path
            ⟨ctx.criticalPath.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)).subgroupOf
              (VAt ctx.Γ ctx.criticalPath.a')).map
                (QuotientGroup.mk'
                  ((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a')))) :
    let R := ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers (selected : G)⁆
    ⁅K, ZAt ctx.Γ neighbor⁆ ≤ R ⊔ ZAt ctx.Γ ctx.criticalPath.a' ∧
      R ≤ VAt ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.a'
  let U := VAt Γ cp.a'
  let Z := ZAt Γ cp.a'
  let W := U ⧸ Z.subgroupOf U
  let projection := QuotientGroup.mk' (Z.subgroupOf U)
  let C := Subgroup.zpowers (selected : G)
  let R := ⁅U, C⁆
  let line := commutatorAction (Subgroup.zpowers (action.rangeRestrict selected)) W
  let penultimate := cp.path ⟨cp.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let oldCenter := ((ZAt Γ penultimate).subgroupOf U).map projection
  have hshort : 1 < cp.length := by change 4 < cp.length at hb; omega
  have hPU : P ≤ Subgroup.normalizer (U : Set G) := stabilizer_le_normalizer_v Γ cp.a'
  have hCP : C ≤ P := Subgroup.zpowers_le.mpr selected.property
  have hfirstContain := (lemma_seven_four ctx.sectionSeven Γ cp).first_containment
  have hRfirst : R ≤ VAt Γ cp.firstStep := by
    change ⁅U, C⁆ ≤ VAt Γ cp.firstStep
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono
      (Subgroup.zpowers_le.mpr (hfirstContain.1 hselected)) le_rfl).trans
        (Subgroup.le_normalizer_iff_commutator_le_left.mp
          ((lemma_seven_four ctx.sectionSeven Γ cp).reverse_containment.2.trans
            (stabilizer_le_normalizer_v Γ cp.firstStep)))
  let _ : IsElementaryAbelian 2 (VAt Γ cp.firstStep) :=
    ((lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).longer_case hshort).1
  have hselectedPow : selected ^ 2 = 1 :=
    Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (selected : G)
      (hfirstContain.1 hselected))
  have hselectedImage : _root_.IsInvolution (action.rangeRestrict selected) := by
    constructor
    · intro heq
      have hker : selected ∈ action.ker := congrArg Subtype.val heq
      rw [hkernel] at hker
      apply hselectedNot
      change (selected : G) ∈ ctx.Γ.twoCoreAt cp.a'
      rw [ctx.Γ.twoCoreAt_def]
      exact Subgroup.mem_map_of_mem P.subtype hker
    · rw [← map_pow, hselectedPow, map_one]
  have hCnative : C.subgroupOf P = Subgroup.zpowers selected := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hCP, MonoidHom.map_zpowers]
    rfl
  have hlineImage : line = (R.subgroupOf U).map projection := by
    have h := Subgroup.quotient_conjugation_commutatorAction_eq_image P U Z C
      hPU hCP hN action hformula
    rw [hCnative, MonoidHom.map_zpowers] at h
    change commutatorAction (Subgroup.zpowers (action.rangeRestrict selected)) W = _
    rw [← commutatorAction_map_actor_subtype action.range
      (Subgroup.zpowers (action.rangeRestrict selected)), MonoidHom.map_zpowers]
    exact h
  have hKcentral : K ≤ Subgroup.centralizer (ZAt Γ penultimate : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hmodules
  have hneighborU : ZAt Γ neighbor ≤ U := by
    change ZAt Γ neighbor ≤ VAt Γ cp.a'
    rw [VAt, v, Γ.vAt_def]
    exact le_sSup ⟨neighbor, hneighbor, rfl⟩
  have hcontrol : ∀ mover : P, (mover : G) ∈ K → ∀ point : U,
      (point : G) ∈ ZAt Γ neighbor →
      (projection point)⁻¹ * action mover (projection point) ∈
        (R.subgroupOf U).map projection := by
    intro mover hmover point hpoint
    have hcommute : Commute mover selected := by
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp (hKinitial hmover) selected hselected).symm
    have hfactorControl := (SectionOne.oneSevenFactor_commuting_involution_support_control
      hyp D hD _ hselectedD hselectedImage _ (hcommute.map action.rangeRestrict)).2
    let delta : W →* W :=
      { toFun := fun value => value⁻¹ * action mover value
        map_one' := by simp
        map_mul' := by
          intro left right
          simp only [map_mul, mul_inv_rev]
          ac_rfl }
    have hsupportControl : commutatorAction D W ≤ line.comap delta := by
      intro value hvalue
      exact hfactorControl value hvalue
    have hcenterControl : oldCenter ≤ line.comap delta := by
      rintro value ⟨oldPoint, holdPoint, rfl⟩
      have hcomm := Subgroup.mem_centralizer_iff.mp (hKcentral hmover) oldPoint holdPoint
      have hfixed : action mover (projection oldPoint) = projection oldPoint := by
        rw [hformula]
        apply congrArg projection
        apply Subtype.ext
        change (mover : G) * (oldPoint : G) * (mover : G)⁻¹ = (oldPoint : G)
        change (oldPoint : G) * (mover : G) = (mover : G) * (oldPoint : G) at hcomm
        rw [← hcomm, mul_inv_cancel_right]
      change (projection oldPoint)⁻¹ * action mover (projection oldPoint) ∈ line
      rw [hfixed, inv_mul_cancel]
      exact line.one_mem
    rw [← hlineImage]
    exact (sup_le hsupportControl hcenterControl)
      (hsupport (Subgroup.mem_map_of_mem projection hpoint))
  exact ⟨Subgroup.quotient_conjugation_commutator_le_sup P U Z (ZAt Γ neighbor) K R
    hPU hKP hneighborU action hformula hcontrol, hRfirst⟩

/-- The original one-step-neighborhood form follows from its abelianness. -/
public theorem nine_ten_subgroup_displacement_bound
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 4 < ctx.criticalPath.length)
    (K : Subgroup G)
    (hKneighborhood : K ≤ GeneratedNeighborhoodV ctx.Γ ctx.criticalPath.a)
    (hKP : K ≤ GAt ctx.Γ ctx.criticalPath.a')
    (neighbor : ctx.Γ.Vertex)
    (hneighbor : neighbor ∈ neighborhood ctx.Γ ctx.criticalPath.a')
    (hmodules : ⁅K,
      ZAt ctx.Γ (ctx.criticalPath.path
        ⟨ctx.criticalPath.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)⁆ = ⊥)
    (selected : GAt ctx.Γ ctx.criticalPath.a')
    (hselected : (selected : G) ∈ ZAt ctx.Γ ctx.criticalPath.a)
    (hselectedNot : (selected : G) ∉ QAt ctx.Γ ctx.criticalPath.a')
    [hN : ((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a')).Normal]
    [hW : IsElementaryAbelian 2 (VAt ctx.Γ ctx.criticalPath.a' ⧸
      (ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a'))]
    (action : GAt ctx.Γ ctx.criticalPath.a' →* MulAut
      (VAt ctx.Γ ctx.criticalPath.a' ⧸
        (ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a')))
    (hformula : ∀ mover : GAt ctx.Γ ctx.criticalPath.a', ∀ point : VAt ctx.Γ ctx.criticalPath.a',
      action mover (QuotientGroup.mk'
        ((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a')) point) =
        QuotientGroup.mk'
          ((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a'))
          ⟨(mover : G) * (point : G) * (mover : G)⁻¹,
            (Subgroup.mem_normalizer_iff.mp
              (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.a' mover.property)
                point).mp point.property⟩)
    (hkernel : action.ker = pCore 2 (GAt ctx.Γ ctx.criticalPath.a'))
    (hyp : SectionOne.Hypotheses action.range (VAt ctx.Γ ctx.criticalPath.a' ⧸
      (ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a')))
    (D : Subgroup action.range)
    (hD : SectionOne.IsOneSevenFactor
      (V := VAt ctx.Γ ctx.criticalPath.a' ⧸
        (ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a')) D)
    (hselectedD : action.rangeRestrict selected ∈ D)
    (hsupport :
      ((ZAt ctx.Γ neighbor).subgroupOf (VAt ctx.Γ ctx.criticalPath.a')).map
          (QuotientGroup.mk'
            ((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a'))) ≤
        commutatorAction D (VAt ctx.Γ ctx.criticalPath.a' ⧸
          (ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a')) ⊔
          ((ZAt ctx.Γ (ctx.criticalPath.path
            ⟨ctx.criticalPath.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)).subgroupOf
              (VAt ctx.Γ ctx.criticalPath.a')).map
                (QuotientGroup.mk'
                  ((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a')))) :
    let R := ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers (selected : G)⁆
    ⁅K, ZAt ctx.Γ neighbor⁆ ≤ R ⊔ ZAt ctx.Γ ctx.criticalPath.a' ∧
      R ≤ VAt ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let neighborhood := GeneratedNeighborhoodV Γ cp.a
  have habelian := nine_eight_neighborhood_abelian ctx.toLocalContext hb cp.a
  have hZnear : ZAt Γ cp.a ≤ neighborhood :=
    (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1.trans
      (nine_eight_v_le_generated_neighborhood Γ
        ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj))
  have hcentral : K ≤ Subgroup.centralizer (ZAt Γ cp.a : Set G) := hKneighborhood.trans
    ((Subgroup.le_centralizer_iff_isMulCommutative.mpr habelian).trans
      (Subgroup.centralizer_le hZnear))
  exact nine_ten_subgroup_displacement_bound_of_initial_center_centralization ctx hb K
    hcentral hKP neighbor hneighbor hmodules selected hselected hselectedNot action hformula
      hkernel hyp D hD hselectedD hsupport

end Stellmacher.SectionNine
