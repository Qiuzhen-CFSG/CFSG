module
public import Stellmacher.SectionNine.NineFourFactorResidualImage
public import Stellmacher.SectionNine.NineFourAuxiliaryResidualSupport
public import Stellmacher.SectionOne.QuotientConjugationSelectedSupport
public import Stellmacher.SectionOne.OneSevenTransvectionSupportSelection
public import Stellmacher.SectionNine.NineResidualImageOddCore

/-!
# The canonical support lies in the noncentral auxiliary module

In the normalized source (9.4) setup, suppose that V_y is larger than
Z_next. The canonical factor supplied by the literal transvection action
has a lifted support of order eight inside V_y. It contains Z_next and is
normalized by the next stabilizer's two-residual. The theorem consumes the
exact supplied quotient normality witness, elementary-module instance,
action formula, kernel, involution, and canonical-factor data.

The factor-image producers identify the auxiliary residual image as the
conjugate closure of the selected derived factor. The actual V_y is
F-invariant and its residual action is nonzero modulo Z_next. The quotient
support-detection theorem therefore puts the selected support inside the
image of V_y; pulling back uses Z_next≤V_y. Its four-element quotient
support and order-two center give order eight. The local residual maps into
the odd core, which preserves every canonical factor support, giving the
last normalization assertion.

This proves V₁≤V_a in the noncentral paragraph of Stellmacher (9.4), printed
p.51/PDF p.41 of `refs/files/stellmacher-n-group.pdf`. The later equality
V_a=V₁ and geometric intersection identity are separate remaining steps.
-/

open scoped commutatorElement
namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_four_noncentral_support_containment
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A0 B0 : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A0 B0)
    (hb : 1 < ctx.criticalPath.length)
    (remote : ctx.Γ.Vertex)
    (hdistance : ctx.Γ.distance remote ctx.criticalPath.firstStep = 2)
    (actor : G)
    (hactor : actor ∈ GAt ctx.Γ ctx.criticalPath.firstStep ∧
      actor ∈ Subgroup.centralizer (VAt ctx.Γ remote : Set G))
    (conjugator : G)
    (hconjugator : conjugator ∈ ⁅EAt ctx.Γ ctx.criticalPath.firstStep, Subgroup.zpowers actor⁆)
    (hremote : ctx.Γ.act conjugator remote ∈ Neighborhood ctx.Γ ctx.criticalPath.a)
    (hne : ctx.Γ.act conjugator remote ≠ ctx.criticalPath.firstStep)
    (hgenerate : (GAt ctx.Γ ctx.criticalPath.firstStep ⊓ GAt ctx.Γ ctx.criticalPath.a) ⊔
      Subgroup.zpowers actor = GAt ctx.Γ ctx.criticalPath.firstStep)
    (A : Subgroup G) (hA : A ≤ VAt ctx.Γ (ctx.Γ.act conjugator remote))
    (hcomm : ⁅A, Subgroup.zpowers actor⁆ ≤ VAt ctx.Γ ctx.criticalPath.firstStep)
    (y : G) (hy : y ∈ A)
    (hnoncentral :
      let F := (QAt ctx.Γ ctx.criticalPath.a ⊓
        QAt ctx.Γ (ctx.Γ.act conjugator remote)) ⊔ Subgroup.zpowers actor
      let Q := twoCoreIn (twoResidualIn F)
      ⁅Subgroup.zpowers y ⊔ VAt ctx.Γ ctx.criticalPath.firstStep,Q⁆ ⊔
        ZAt ctx.Γ ctx.criticalPath.firstStep ≠ ZAt ctx.Γ ctx.criticalPath.firstStep)
    (hN : ((ZAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf
      (VAt ctx.Γ ctx.criticalPath.firstStep)).Normal) :
    let _ := hN
    let P := GAt ctx.Γ ctx.criticalPath.firstStep
    let U := VAt ctx.Γ ctx.criticalPath.firstStep
    let Z := ZAt ctx.Γ ctx.criticalPath.firstStep
    ∀ hW : IsElementaryAbelian 2 (U ⧸ Z.subgroupOf U),
    let _ := hW
    ∀ action : P →* MulAut (U ⧸ Z.subgroupOf U),
      (∀ mover : P, ∀ point : U,
        action mover (QuotientGroup.mk' (Z.subgroupOf U) point) =
          QuotientGroup.mk' (Z.subgroupOf U)
            ⟨(mover:G)*(point:G)*(mover:G)⁻¹,
              (Subgroup.mem_normalizer_iff.mp
                (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.firstStep mover.property)
                point).mp point.property⟩) →
      action.ker = pCore 2 P →
      _root_.IsInvolution (action ⟨actor,hactor.1⟩) →
      let D := ⁅SectionOne.oddCore action.range,
        Subgroup.zpowers (action.rangeRestrict ⟨actor,hactor.1⟩)⁆ ⊔
          Subgroup.zpowers (action.rangeRestrict ⟨actor,hactor.1⟩)
      SectionOne.IsOneSevenFactor (V := U ⧸ Z.subgroupOf U) D →
      let F := (QAt ctx.Γ ctx.criticalPath.a ⊓
        QAt ctx.Γ (ctx.Γ.act conjugator remote)) ⊔ Subgroup.zpowers actor
      let Q := twoCoreIn (twoResidualIn F)
      let V_y := ⁅Subgroup.zpowers y ⊔ U,Q⁆ ⊔ Z
      let support := ((commutatorAction D (U ⧸ Z.subgroupOf U)).comap
        (QuotientGroup.mk' (Z.subgroupOf U))).map U.subtype
      Z ≤ support ∧ support ≤ V_y ∧ Nat.card support = 8 ∧
        EAt ctx.Γ ctx.criticalPath.firstStep ≤ Subgroup.normalizer (support : Set G) := by
  let _ := hN
  dsimp only
  intro hW
  let _ := hW
  intro action hact hkernel hinvolution hfactor
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let U := VAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  let d := Γ.act conjugator remote
  let R0 := QAt Γ cp.a ⊓ QAt Γ d
  let F := R0 ⊔ Subgroup.zpowers actor
  let R := twoResidualIn F
  let Q := twoCoreIn R
  let W := ⁅Subgroup.zpowers y ⊔ U,Q⁆ ⊔ Z
  let f := action.rangeRestrict
  let D := ⁅SectionOne.oddCore action.range, Subgroup.zpowers (f ⟨actor,hactor.1⟩)⁆ ⊔
    Subgroup.zpowers (f ⟨actor,hactor.1⟩)
  let B := (R0.subgroupOf P).map f
  let V := U ⧸ Z.subgroupOf U
  let q : U →* V := QuotientGroup.mk' (Z.subgroupOf U)
  let supportBar := commutatorAction D V
  let support := (supportBar.comap q).map U.subtype
  have hkernelF : f.ker = pCore 2 P := (MonoidHom.ker_rangeRestrict action).trans hkernel
  have hinvF : _root_.IsInvolution (f ⟨actor,hactor.1⟩) :=
    ⟨fun heq => hinvolution.1 (congrArg Subtype.val heq), Subtype.ext hinvolution.2⟩
  have hpacket := nine_four_factor_le_auxiliary_image ctx hb remote hdistance actor hactor
    conjugator hconjugator hremote hne hgenerate f action.rangeRestrict_surjective hkernelF hinvF hfactor.1
  have hclosure := nine_four_factor_residual_image ctx hb remote hdistance actor hactor
    conjugator hconjugator hremote hne hgenerate f action.rangeRestrict_surjective hkernelF hinvF hfactor
  have hgeom := nine_four_auxiliary_core_geometry ctx hb d actor hactor.1
  have hFP : F ≤ P := hgeom.1
  have hRP : R ≤ P := (twoResidualIn_le F).trans hFP
  have hPU : P ≤ Subgroup.normalizer U := stabilizer_le_normalizer_v Γ cp.firstStep
  have hnorm := nine_four_auxiliary_normalization ctx hb d hremote actor hactor.1
    (Subgroup.zpowers y) (Subgroup.zpowers_le.mpr (hA hy))
    ((Subgroup.commutator_mono (Subgroup.zpowers_le.mpr hy) le_rfl).trans hcomm)
  have hZcard := (nine_next_center_commutator_and_kernel ctx hb cp.firstStep
    ⟨1,Γ.act_one _⟩).1
  have hnextZa : Z ≤ ZAt Γ cp.a :=
    ((nine_seven_center_join ctx cp.a ⟨1,Γ.act_one _⟩).2 cp.firstStep
      ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj)).2
  have hZU : Z ≤ U := hnextZa.trans (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1
  have hWle : W ≤ U := sup_le
    ((Subgroup.commutator_mono le_rfl ((twoCoreIn_le R).trans (twoResidualIn_le F))).trans
      hnorm.2) hZU
  have hFW : F ≤ Subgroup.normalizer W :=
    (nine_four_auxiliary_residual_support ctx hb d hremote actor hactor.1 A hA hcomm y hy).1
  have hBF : B ≤ (F.subgroupOf P).map f :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono P le_sup_left)
  have hactive : ¬ ⁅W,R⁆ ≤ Z :=
    nine_four_auxiliary_residual_active ctx hb d hremote actor hactor.1 A hA hcomm y hy hnoncentral
  have hsupport := SectionOne.quotient_conjugation_selected_support_le
    P U Z F R W hRP hWle hPU hFW hN hW action hact D B hfactor hpacket.1 hBF hclosure hactive
  have hker : q.ker ≤ W.subgroupOf U := by
    rw [show q.ker = Z.subgroupOf U from QuotientGroup.ker_mk' _]
    exact Subgroup.subgroupOf_mono U le_sup_right
  have hsupportW : support ≤ W := by
    have hh := Subgroup.comap_mono (f:=q) hsupport
    rw [Subgroup.comap_map_eq_self hker] at hh
    exact (Subgroup.map_mono (f:=U.subtype) hh).trans_eq
      (Subgroup.map_subgroupOf_eq_of_le hWle)
  have hbasic := Subgroup.lift_support_basic U Z hZU supportBar
  have hEP : EAt Γ cp.firstStep ≤ P := by
    rw [EAt,CosetGraphContext.e,Γ.twoResidualAt_def]
    exact twoResidualIn_le _
  have hodd := nine_local_residual_image_le_oddCore ctx.toLocalContext cp.firstStep cp.a
    (Γ.adjacent_symm cp.firstStep_adj) f action.rangeRestrict_surjective hkernelF.ge
  have hinvariant := SectionOne.oneSevenFactor_support_oddCore_invariant D hfactor
  have hnormal : EAt Γ cp.firstStep ≤ Subgroup.normalizer support := by
    apply Subgroup.lift_support_normalizes P U Z _ hEP hPU action hact supportBar
    intro mover hmover
    let oddMover : SectionOne.oddCore action.range :=
      ⟨f mover,hodd (Subgroup.mem_map_of_mem f hmover)⟩
    ext point
    constructor
    · rintro ⟨source,hsource,rfl⟩
      exact (hinvariant.invariant oddMover source).mp hsource
    · intro hpoint
      refine ⟨(action mover).symm point,?_,(action mover).apply_symm_apply point⟩
      apply (hinvariant.invariant oddMover ((action mover).symm point)).mpr
      change (action mover) ((action mover).symm point) ∈ supportBar
      simpa only [MulEquiv.apply_symm_apply] using hpoint
  refine ⟨hbasic.2.1,hsupportW,?_,hnormal⟩
  rw [hbasic.2.2.1,hfactor.2.2.1,hZcard]

end Stellmacher.SectionNine
