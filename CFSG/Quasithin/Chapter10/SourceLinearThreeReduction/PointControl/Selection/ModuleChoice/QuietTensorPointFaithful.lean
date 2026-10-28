module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietTensorPointCubic
public import Theory.Representation.BinaryConjugationSection.ReducedImage
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.OffenderSubgroup
public import Theory.Representation.BinaryTensorThree.PointFlagMovement

/-!
# The faithful offender on the original point section

The full section-action kernel is compared with the actual centralizer
in the quotient by the point. G.2.2 reducedness therefore gives a trivial
two-core in the faithful image, with its SQTK cover supplied by C_G(z).

The original V-image acts faithfully. Its kernel preimage in V is an
XT-invariant subgroup containing V₅. Upper-layer irreducibility makes
this either V₅ or V. The latter would kill both generating conjugates
and hence K_z, contradicting the lifted cubic movement of V₅/⟨z⟩.
Thus the same actor retains order sixteen and is a quadratic offender
on the same vector space. The complete adequate B.5 classification now
applies to its nontrivial offender-generated subgroup.

The Source application constructs all these data on the original
U/⟨z⟩ of dimension at most eight. Identifying the two natural summands
and choosing their common diagonal cubic remain separate proof steps;
the entire C_G(z)/O₂(C_G(z)) action is not asserted faithful here.
Source: Aschbacher--Smith G.2.2, B.5.6 and 8.3.12, pp.332,105,726.
-/

public noncomputable section


open scoped commutatorElement
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02 Chapter8.Section03 Chapter1 BinaryTensorThree
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)
variable (q : localJoin T L →* PointParabolic.Actor) (hq : Function.Surjective q)
  (b : Additive D.fullModule ≃ₗ[ZMod 2] Space)
  (hb : ∀ (a : localJoin T L) (v : Additive D.fullModule),
    quietTensorLinearAction D b a (b v) = action (PointParabolic.tensorHom (q a)) (b v))
  {z : G} (hzV : z ∈ D.fullModule)
  (hbz : b (Additive.ofMul ⟨z,hzV⟩) = point)
  (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) (hz1 : z ≠ 1)

include hq hb hbz hzT hz1 in
/-- The full faithful image of the original section has trivial two-core. -/
theorem quiet_tensor_point_faithful_image_twoCore
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2)
      ((quietTensorPointFlagSetup D b z).H ⧸ pCore 2 (quietTensorPointFlagSetup D b z).H) W)
    (c : Representation.BinaryConjugationSection (quietTensorPointFlagSetup D b z).H
      (quietTensorPointFlagSetup D b z).U (zpowers z)
      (σ.comp (QuotientGroup.mk' (pCore 2 (quietTensorPointFlagSetup D b z).H)))) :
    pCore 2 (actionImage σ) = ⊥ := by
  let s := quietTensorPointFlagSetup D b z
  have hs := quiet_tensor_point_flag_hypothesis D q hq b hb hzV hbz hzT hz1
  let f : s.H →* s.tilde s.H := {
    toFun x := ⟨QuotientGroup.mk' (s.V₁.subgroupOf s.G₁) ⟨x,hs.H_le x.property⟩,
      ⟨⟨x,hs.H_le x.property⟩,x.property,rfl⟩⟩
    map_one' := Subtype.ext (map_one _)
    map_mul' x y := Subtype.ext (map_mul (QuotientGroup.mk' (s.V₁.subgroupOf s.G₁))
      (⟨x,hs.H_le x.property⟩ : s.G₁) ⟨y,hs.H_le y.property⟩) }
  have hf : Function.Surjective f := by
    rintro ⟨y,x,hx,rfl⟩
    exact ⟨⟨x,hx⟩,rfl⟩
  have hk : f.ker = (zpowers z).subgroupOf s.H := by
    ext x
    change f x = 1 ↔ (x:G) ∈ zpowers z
    rw [Subtype.ext_iff]
    exact QuotientGroup.eq_one_iff (⟨x,hs.H_le x.property⟩ : s.G₁)
  have hm : (s.U.subgroupOf s.H).map f = (s.tilde s.U).subgroupOf (s.tilde s.H) := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,hs.H_le x.property⟩,hx,rfl⟩
    · rintro ⟨x,hx,hxy⟩
      exact ⟨⟨x,hs.U_le_H hx⟩,hx,Subtype.ext hxy⟩
  have hi : actionImage (σ.comp (QuotientGroup.mk' (pCore 2 s.H))) = actionImage σ := by
    ext a
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨QuotientGroup.mk' (pCore 2 s.H) x,rfl⟩
    · rintro ⟨x,rfl⟩
      obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 s.H) x
      exact ⟨y,rfl⟩
  rw [←hi]
  exact c.actionImage_twoCore_eq_bot_of_reduced_image f hk hf
    (hm.symm ▸ hs.tilde_U_reduced)

include hq hb hbz hzT hz1 in
/-- G.2.2 and the genuine point-centralizer cover discharge the B.5 action inputs. -/
theorem quiet_tensor_point_faithful_image_classification
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2)
      ((quietTensorPointFlagSetup D b z).H ⧸ pCore 2 (quietTensorPointFlagSetup D b z).H) W)
    (c : Representation.BinaryConjugationSection (quietTensorPointFlagSetup D b z).H
      (quietTensorPointFlagSetup D b z).U (zpowers z)
      (σ.comp (QuotientGroup.mk' (pCore 2 (quietTensorPointFlagSetup D b z).H)))) :
    let τ := imageRepresentation σ
    ChapterB.SourceInduction.AdequateAlternative (τ.comp (offenderSubgroup τ).subtype) := by
  dsimp only
  let s := quietTensorPointFlagSetup D b z
  let f := (actionHom σ).comp (QuotientGroup.mk' (pCore 2 s.H))
  let τ := imageRepresentation σ
  let : Finite W := Finite.of_surjective (fun u : s.U => (c.coordinates u).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  have hcore := quiet_tensor_point_faithful_image_twoCore D q hq b hb hzV hbz hzT hz1 σ c
  have hsq : IsSQTK KnownSimple.IsKnownSimple s.H := D.simpleQTKE.twoLocal_sqtk
    (isTwoLocal_involution_centralizer (orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian z hzV) hz1))
  let cover : ChapterB.SourceInduction.SQTKQuotient KnownSimple.IsKnownSimple (actionImage σ) := {
    Cover := s.H
    kernel := f.ker
    sqtk := hsq
    equiv := QuotientGroup.quotientKerEquivOfSurjective _
      (σ.asGroupHom.rangeRestrict_surjective.comp (QuotientGroup.mk'_surjective _)) }
  exact ChapterB.SourceInduction.offenderSubgroup_adequateAlternative τ
    (imageRepresentation_injective σ) hcore cover
include hq hb hbz hzT in
/-- The original residual X genuinely moves the five-space modulo the fixed point. -/
theorem quiet_tensor_point_seed_moved :
    ¬ ⁅CentralizerSetup.X ⟨T,localOrbit T L,z⟩,quietTensorFive D b⁆ ≤ zpowers z := by
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  have hXT := quiet_XT_eq_point_centralizer (T := T) (L := L) hzT
  have hXJ : d.XT ≤ localJoin T L := hXT.le.trans inf_le_left
  have hfix (a : localJoin T L) :
      q a ∈ PointParabolic.PairP ↔ (a:G) ∈ centralizer ({z} : Set G) := by
    rw [←PointParabolic.fixes_point_iff]
    have hh := hb a (Additive.ofMul ⟨z,hzV⟩)
    rw [quietTensorLinearAction_apply,hbz] at hh
    rw [←hh,←hbz,b.injective.eq_iff,Additive.ofMul.injective.eq_iff,Subtype.ext_iff]
    change (a:G)*z*(a:G)⁻¹ = z ↔ _
    rw [mem_centralizer_singleton_iff,mul_inv_eq_iff_eq_mul]
  let f : d.XT →* PointParabolic.PairP :=
    (q.comp (inclusion hXJ)).codRestrict _ (fun a =>
      (hfix (inclusion hXJ a)).mpr (hXT.le a.property).2)
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨x,hx⟩ := hq a
    have hxz := (hfix x).mp (hx ▸ a.property)
    exact ⟨⟨x,hXT.ge ⟨x.property,hxz⟩⟩,Subtype.ext hx⟩
  obtain ⟨a,ha,w,hw,hm⟩ := PointFlag.exists_cubic_moving_lower
  have har : a ∈ pResidual 2 PointParabolic.PairP :=
    mem_pResidual_of_orderOf_coprime
      ((by decide : Nat.Coprime 2 3).of_dvd_right (orderOf_dvd_of_pow_eq_one ha))
  rw [←map_pResidual_of_surjective 2 f hf] at har
  obtain ⟨x,hxr,hxa⟩ := har
  have hxX : (x:G) ∈ d.X := by
    rw [←quiet_point_residual_eq (T := T) (L := L) hzT]
    exact mem_map_of_mem d.XT.subtype hxr
  obtain ⟨v,rfl⟩ := b.surjective w
  have hv5 : (v.toMul:G) ∈ quietTensorFive D b :=
    (mem_quietTensorFive D b v.toMul).mpr hw
  intro hcomm
  have hcv : ⁅(x:G),(v.toMul:G)⁆ ∈ zpowers z :=
    hcomm (commutator_mem_commutator hxX hv5)
  have hN : localJoin T L ≤ normalizer (D.fullModule : Set G) :=
    (sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)).trans
      D.maximalLocal_normalizes_fullModule
  let xv : D.fullModule := ⟨(x:G)*(v.toMul:G)*(x:G)⁻¹,
    le_normalizer_iff.mp hN x (hXJ x.property) v.toMul v.toMul.property⟩
  have hline : b (Additive.ofMul (xv * v.toMul⁻¹)) ∈ PointFlag.line := by
    obtain ⟨n,hn⟩ := mem_zpowers_iff.mp hcv
    have he : xv * v.toMul⁻¹ = (⟨z,hzV⟩ : D.fullModule)^n := Subtype.ext hn.symm
    rw [he]
    change b (n • Additive.ofMul (⟨z,hzV⟩ : D.fullModule)) ∈ PointFlag.line
    rw [map_zsmul,hbz]
    exact PointFlag.line.toAddSubgroup.zsmul_mem ((PointFlag.mem_line_iff _).mpr (Or.inr rfl)) n
  apply hm
  have hact := hb (inclusion hXJ x) v
  rw [quietTensorLinearAction_apply] at hact
  have hxq : q (inclusion hXJ x) = (a:PointParabolic.Actor) := congrArg Subtype.val hxa
  rw [hxq] at hact
  change b (Additive.ofMul xv) = _ at hact
  rw [ofMul_mul,ofMul_inv,←sub_eq_add_neg] at hline
  rw [map_sub,hact] at hline
  exact hline

include hq hb hbz hzT hz1 in
/-- Upper irreducibility and the original two generators kill the offender kernel. -/
theorem quiet_tensor_point_offender_faithful
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2)
      ((quietTensorPointFlagSetup D b z).H ⧸ pCore 2 (quietTensorPointFlagSetup D b z).H) W)
    (c : Representation.BinaryConjugationSection (quietTensorPointFlagSetup D b z).H
      (quietTensorPointFlagSetup D b z).U (zpowers z)
      (σ.comp (QuotientGroup.mk' (pCore 2 (quietTensorPointFlagSetup D b z).H))))
    (k : CentralizerSetup.Kz ⟨T,localOrbit T L,z⟩)
    (hgen : let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
      let π := QuotientGroup.mk' (pCore 2 d.Gz)
      let A := (D.fullModule.subgroupOf d.Gz).map π
      A ⊔ A.map (MulAut.conj (π (inclusion d.Kz_le_Gz k))).toMonoidHom =
        (d.Kz.subgroupOf d.Gz).map π) :
    let s := quietTensorPointFlagSetup D b z
    let π := QuotientGroup.mk' (pCore 2 s.H)
    let A := (D.fullModule.subgroupOf s.H).map π
    ∀ a ∈ A, (∀ w, σ a w = w) → a = 1 := by
  dsimp only
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  let s := quietTensorPointFlagSetup D b z
  let π := QuotientGroup.mk' (pCore 2 s.H)
  let ρ := σ.comp π
  let N := ρ.ker.map s.H.subtype
  let E := D.fullModule ⊓ N
  have hs := quiet_tensor_point_flag_hypothesis D q hq b hb hzV hbz hzT hz1
  have h5Q : quietTensorFive D b ≤ s.H.pCoreIn 2 :=
    (le_conjugateSpanBy _ _).trans hs.U_le_core
  have hQN : s.H.pCoreIn 2 ≤ N := by
    rintro _ ⟨a,ha,rfl⟩
    refine ⟨a,?_,rfl⟩
    change σ (π a) = 1
    rw [show π a = 1 from (QuotientGroup.eq_one_iff a).mpr ha,map_one]
  have h5E : quietTensorFive D b ≤ E := le_inf (quietTensorFive_le D b) (h5Q.trans hQN)
  have hXT := quiet_XT_eq_point_centralizer (T := T) (L := L) hzT
  have hXN : d.XT ≤ normalizer (N : Set G) := by
    apply (sup_le (d.X_le.trans inf_le_right) hzT).trans
    change s.H ≤ normalizer (N : Set G)
    simpa only [N,normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype]
      using ρ.ker.le_normalizer_map s.H.subtype
  have hVN : d.XT ≤ normalizer (D.fullModule : Set G) :=
    (hXT.le.trans inf_le_left).trans
      ((sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)).trans
        D.maximalLocal_normalizes_fullModule)
  have hEN : d.XT ≤ normalizer (E : Set G) :=
    (le_inf hVN hXN).trans inf_normalizer_le_normalizer_inf
  have hE : E = quietTensorFive D b := by
    rcases quiet_tensor_point_upper_irreducible D q hq b hb hzV hbz hzT
      E h5E inf_le_left hEN with he | he
    · exact he
    · have hVN' : D.fullModule ≤ N := he ▸ (show E ≤ N from inf_le_right)
      have hA : (D.fullModule.subgroupOf s.H).map π ≤ σ.ker := by
        rintro _ ⟨v,hv,rfl⟩
        obtain ⟨a,ha,hav⟩ := hVN' hv
        have hav' : a = v := Subtype.ext hav
        exact hav' ▸ ha
      have hAg : ((D.fullModule.subgroupOf s.H).map π).map
          (MulAut.conj (π (inclusion d.Kz_le_Gz k))).toMonoidHom ≤ σ.ker := by
        rintro _ ⟨a,ha,rfl⟩
        exact (inferInstance : σ.ker.Normal).conj_mem a (hA ha) _
      have hK : (d.Kz.subgroupOf s.H).map π ≤ σ.ker :=
        hgen ▸ sup_le hA hAg
      apply (quiet_tensor_point_seed_moved D q hq b hb hzV hbz hzT).elim
      apply commutator_le.mpr
      intro x hx v hv
      have hxH : x ∈ s.H := d.Kz_le_Gz (le_conjugateSpanBy d.X d.Gz hx)
      have hxker : (⟨x,hxH⟩ : s.H) ∈ ρ.ker :=
        hK (mem_map_of_mem π (le_conjugateSpanBy d.X d.Gz hx))
      exact (c.action_mem_ker_iff _).mp hxker v (le_conjugateSpanBy _ _ hv)
  intro a ha hfix
  obtain ⟨v,hv,rfl⟩ := ha
  have hvker : v ∈ ρ.ker := LinearMap.ext hfix
  have hvE : (v:G) ∈ E := ⟨hv,mem_map_of_mem s.H.subtype hvker⟩
  have hvQ := h5Q (hE ▸ hvE)
  obtain ⟨u,hu,huv⟩ := hvQ
  have huv' : u = v := Subtype.ext huv
  exact (QuotientGroup.eq_one_iff v).mpr (huv' ▸ hu)

include hq hb hbz hzT hz1 in
/-- The literal order-sixteen actor survives faithfully and remains a
quadratic offender in the reduced image. B.5 now has its nontrivial full
alternatives on the same vector space, with no classification premise. -/
theorem quiet_tensor_point_faithful_offender_classification
    (hcore : ¬ D.fullModule ≤ (centralizer ({z} : Set G)).pCoreIn 2)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2)
      ((quietTensorPointFlagSetup D b z).H ⧸ pCore 2 (quietTensorPointFlagSetup D b z).H) W)
    (c : Representation.BinaryConjugationSection (quietTensorPointFlagSetup D b z).H
      (quietTensorPointFlagSetup D b z).U (zpowers z)
      (σ.comp (QuotientGroup.mk' (pCore 2 (quietTensorPointFlagSetup D b z).H))))
    (hc : Nat.card (quietTensorPointFlagSetup D b z).U ≤ 512)
    (k : CentralizerSetup.Kz ⟨T,localOrbit T L,z⟩)
    (hgen : let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
      let π := QuotientGroup.mk' (pCore 2 d.Gz)
      let A := (D.fullModule.subgroupOf d.Gz).map π
      A ⊔ A.map (MulAut.conj (π (inclusion d.Kz_le_Gz k))).toMonoidHom =
        (d.Kz.subgroupOf d.Gz).map π) :
    let s := quietTensorPointFlagSetup D b z
    let π := QuotientGroup.mk' (pCore 2 s.H)
    let A := (D.fullModule.subgroupOf s.H).map π
    let τ := imageRepresentation σ
    (∀ a ∈ A, (∀ w, σ a w = w) → a = 1) ∧
      Nat.card (actionSubgroup σ A) = 16 ∧
      IsOffender τ (actionSubgroup σ A) ∧
      IsQuadratic τ (actionSubgroup σ A) ∧
      ChapterB.SourceInduction.NontrivialAdequateAlternative
        (τ.comp (offenderSubgroup τ).subtype) := by
  dsimp only
  let s := quietTensorPointFlagSetup D b z
  let π := QuotientGroup.mk' (pCore 2 s.H)
  let A := (D.fullModule.subgroupOf s.H).map π
  let τ := imageRepresentation σ
  let : Finite W := Finite.of_surjective (fun u : s.U => (c.coordinates u).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  have hf := quiet_tensor_point_offender_faithful D q hq b hb hzV hbz hzT hz1 σ c k hgen
  have hoff := quiet_tensor_point_full_offender D q hq b hb hzV hbz hzT hz1 hcore σ c hc
  have hm : ⁅D.fullModule,s.U⁆ ≤ quietTensorFive D b := by
    rw [commutator_comm]
    exact quiet_tensor_point_closure_commutator D q hq b hb hzV hbz hzT hz1 hcore
  have hfix : ⁅D.fullModule,quietTensorFive D b⁆ ≤ zpowers z := by
    have he : ⁅D.fullModule,quietTensorFive D b⁆ = ⊥ :=
      commutator_eq_bot_iff_le_centralizer.mpr
        ((Subgroup.le_centralizer (H := D.fullModule)).trans
          (centralizer_le (quietTensorFive_le D b)))
    exact he.le.trans bot_le
  have hquad := Representation.BinaryConjugationSection.quadratic_of_commutator_bounds
    σ π c D.fullModule (quietTensorFive D b) hm hfix
  have himg : IsOffender τ (actionSubgroup σ A) := by
    refine ⟨hoff.1.actionSubgroup σ hf,?_⟩
    rw [fixedCodim_actionSubgroup,actionSubgroup_rank σ A hf]
    exact hoff.2
  refine ⟨hf,?_,himg,?_,?_⟩
  · rw [←Nat.card_congr (faithfulActionEquiv σ A hf).toEquiv]
    exact quiet_tensor_point_core_image_card D q hq b hb hzV hbz hzT hz1 hcore
  · rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ w
    exact hquad a ha b hb w
  · obtain ⟨B,hB⟩ := (isFFModule_iff_exists_bestOffender τ).mp ⟨_,himg⟩
    have hn : offenderSubgroup τ ≠ ⊥ := fun he =>
      hB.1.1 (bot_unique ((hB.le_offenderSubgroup τ).trans_eq he))
    let : Nontrivial (offenderSubgroup τ) := (nontrivial_iff_ne_bot _).mpr hn
    exact (quiet_tensor_point_faithful_image_classification D q hq b hb hzV hbz hzT hz1 σ c).of_nontrivial _

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
