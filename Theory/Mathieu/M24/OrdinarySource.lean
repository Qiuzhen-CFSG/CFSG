module
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.TwoCentral
public import Theory.Mathieu.M23.OrdinarySource
public import Theory.SpecificGroups.BinaryLinear.Perfect
public import Theory.SpecificGroups.BinaryLinear.SylowTransvections
public import Theory.GroupTheory.Commutator.PerfectQuotient
public import Theory.GroupTheory.CentralizerSmallKernelTransport
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Mathlib.Tactic.Module

/-!
# Residual control of the original two-central M₂₄ involution centralizer

The supplied two-central hypothesis selects the actual 2A conjugacy class.
No perfectness assertion is made about the other involution class. The 2A
centralizer has its native translation kernel of order sixteen and quotient
the stabilizer of a nonzero vector in GL₄(2). A transvection commutator identity
and the perfect GL₃(2) quotient prove that this vector stabilizer is perfect.

The native M₂₃ point stabilizer fixes a point of the marked octad. Its involution
centralizer is perfect and contains the whole translation kernel, so that
kernel lies in the derived subgroup of the full M₂₄ centralizer. This proves
perfectness of the full centralizer. Its center lies in the self-centralizing
translation kernel and therefore injects into the center of the same literal
M₂₃ point-fixer centralizer. The latter has order two, identifying the ambient
center image with the line of the original marked involution.

Consequently an overgroup whose residual lies in this centralizer equals it:
perfectness first identifies that residual with the centralizer, and preserving
its characteristic center line forces centralization of the involution. This
is precisely the model input consumed by the full central-cover argument in
Aschbacher--Smith 15.1.20(3d), printed p.1097. The original ordinary consumer
supplies the two-central hypothesis and residual containment; no maximality or
overgroup catalogue is assumed. The only new finite reduction is membership of
the distinguished fixed point in the existing marked octad.
-/

public section
open Subgroup MathieuCode
open scoped commutatorElement
noncomputable section
namespace Sporadic.Mathieu.M24InvolutionCentralizers
open M24ChapterHStabilizers Theory.LinearAlgebra BinaryLinear M24LocalGeometry
namespace OrdinarySource
private theorem transvection_cross (w y : OctadAction.Space)
    (α β : OctadAction.Space →ₗ[ZMod 2] ZMod 2)
    (hαw : α w = 0) (hβw : β w = 0) (hβy : β y = 0) (hαy : α y = 1) :
    ⁅transvection w α hαw, transvection y β hβy⁆ = transvection w β hβw := by
  apply LinearEquiv.ext
  intro v
  change (v + β v • y + α (v + β v • y) • w +
    β (v + β v • y + α (v + β v • y) • w) • y +
    α (v + β v • y + α (v + β v • y) • w +
      β (v + β v • y + α (v + β v • y) • w) • y) • w) = v + β v • w
  simp only [map_add, map_smul, hαw, hβw, hβy, hαy, smul_eq_mul, mul_zero,
    mul_one, add_zero]
  match_scalars <;> ring_nf <;>
    simp only [show (2 : ZMod 2) = 0 by decide, show (3 : ZMod 2) = 1 by decide,
      mul_zero, mul_one, zero_add]

/-- Every displacement-kernel element is a commutator inside the point stabilizer. -/
private theorem point_kernel_le_commutator {v : OctadAction.Space} (hv : v ≠ 0) :
    BinaryFivePointStabilizer.kernel v ≤ commutator (BinaryFivePointStabilizer.stabilizer v) := by
  intro g hg
  by_cases hg1 : g = 1
  · exact hg1 ▸ one_mem _
  have hr : g.val ∈ radical (BinaryFivePointStabilizer.line v) :=
    ⟨BinaryFivePointStabilizer.fixes_line v g, (BinaryFivePointStabilizer.mem_kernel_iff v g).mp hg⟩
  obtain ⟨β, _, hβv, he⟩ := exists_transvection_of_mem_line_radical hv hr
    (fun h => hg1 (Subtype.ext h))
  have hline : BinaryFivePointStabilizer.line v ≤ β.ker := by
    rw [Submodule.span_singleton_le_iff_mem]
    exact hβv
  have hlt : BinaryFivePointStabilizer.line v < β.ker := by
    apply lt_of_le_of_ne hline
    intro heq
    have hd := β.finrank_range_add_finrank_ker
    have hb := Submodule.finrank_le β.range
    rw [← heq, finrank_span_singleton hv] at hd
    norm_num [OctadAction.Space] at hd hb
    omega
  obtain ⟨y, hβy, hyv⟩ := SetLike.exists_of_lt hlt
  obtain ⟨α, hαy, hαv⟩ := (BinaryFivePointStabilizer.line v).exists_le_ker_of_notMem hyv
  have hαv0 : α v = 0 := hαv (Submodule.mem_span_singleton_self v)
  have hαy1 : α y = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hαy
  let a : BinaryFivePointStabilizer.stabilizer v := ⟨transvection v α hαv0, by
    change v + α v • v = v
    simp [hαv0]⟩
  let c : BinaryFivePointStabilizer.stabilizer v := ⟨transvection y β hβy, by
    change v + β v • y = v
    simp [hβv]⟩
  have hcomm : ⁅a, c⁆ = g := by
    apply Subtype.ext
    change ⁅transvection v α hαv0, transvection y β hβy⁆ = g.val
    rw [transvection_cross v y α β hαv0 hβv hβy hαy1]
    apply LinearEquiv.ext
    intro x
    exact (he x).symm
  rw [← hcomm]
  exact commutator_mem_commutator (mem_top _) (mem_top _)


private theorem pointStabilizer_isPerfect :
    Group.IsPerfect (BinaryFivePointStabilizer.stabilizer TwoA.markedVector) := by
  let e := BinaryLinear.SmallParabolicLevi.linearGroupCongr TwoA.quotientCoordinates
  let : Group.IsPerfect (BinaryLinear.OuterCyclic.LinearGroup 3) :=
    BinaryLinear.linearGroup_isPerfect 3 (by decide)
  let : Group.IsPerfect (BinaryLinear.GL TwoA.QuotientSpace) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  constructor
  have hh := CentralExtension.ker_sup_commutator_eq_top_of_surjective
    (BinaryFivePointStabilizer.quotientAction TwoA.markedVector)
    (BinaryFivePointStabilizer.quotientAction_surjective TwoA.markedVector)
  rwa [sup_eq_right.mpr (point_kernel_le_commutator TwoA.markedVector_ne_zero)] at hh

private theorem basePoint_mem : (24 : Fin 24) ∈ TwoA.fixedOctad.val := by decide +kernel

private abbrev H := MulAction.stabilizer M24 (24 : Fin 24)
private def pointedInvolution : H :=
  ⟨involution2A, TwoA.fixed_iff _ |>.mpr basePoint_mem⟩
private theorem pointedInvolution_order : orderOf pointedInvolution = 2 :=
  (Subgroup.orderOf_coe pointedInvolution).symm.trans involution2A_order
private abbrev P := centralizer ({pointedInvolution} : Set H)
private def pointedEquiv :=
  Theory.GroupTheory.CentralizerSmallKernelTransport.centralizerEquiv
    m23EquivM24PointStabilizer.symm pointedInvolution
private theorem pointed_isPerfect : Group.IsPerfect P := by
  let : Group.IsPerfect (centralizer
      ({m23EquivM24PointStabilizer.symm pointedInvolution} : Set M23)) :=
    M23Geometry.InvolutionCentralizer.isPerfect_of_involution
      ((m23EquivM24PointStabilizer.symm.orderOf_eq pointedInvolution).trans
        pointedInvolution_order)
  exact Group.IsPerfect.ofSurjective (f := pointedEquiv.symm.toMonoidHom)
    pointedEquiv.symm.surjective
private theorem pointed_center_card : Nat.card (center P) = 2 := by
  exact (Nat.card_congr (centerCongr pointedEquiv).toEquiv).trans
    (M23Geometry.InvolutionCentralizer.center_card_of_involution
      ((m23EquivM24PointStabilizer.symm.orderOf_eq pointedInvolution).trans
        pointedInvolution_order))
private def pointedInclusion : P →* centralizer2A where
  toFun x := ⟨x.val.val, mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property))⟩
  map_one' := rfl
  map_mul' _ _ := rfl
private theorem pointedInclusion_injective : Function.Injective pointedInclusion := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : centralizer2A => z.val) h
private theorem translation_fixes_base (u : TwoA.translationKernel) :
    u.val.val • (24 : Fin 24) = (24 : Fin 24) := by
  have hu : TwoA.toOctad u.val ∈ OctadAction.Core TwoA.fixedOctad := u.property
  rw [OctadAction.Core, CocodeOctad.core_eq_coordinateKernel,
    CocodeOctad.mem_coordinateAction_ker] at hu
  exact hu _ basePoint_mem
private theorem translation_le_commutator :
    TwoA.translationKernel ≤ commutator centralizer2A := by
  let : Group.IsPerfect P := pointed_isPerfect
  intro u hu
  let x : P := ⟨⟨u.val, translation_fixes_base ⟨u, hu⟩⟩,
    mem_centralizer_singleton_iff.mpr
      (Subtype.ext (mem_centralizer_singleton_iff.mp u.property))⟩
  have hm : (commutator P).map pointedInclusion ≤ commutator centralizer2A := by
    rw [map_commutator_eq]
    exact Subgroup.commutator_mono le_top le_top
  have hx : x ∈ commutator P := by
    rw [Group.IsPerfect.commutator_eq_top]
    exact mem_top x
  exact hm (mem_map_of_mem pointedInclusion hx)

/-- The original two-central centralizer, including its full translation kernel, is perfect. -/
theorem twoA_isPerfect : Group.IsPerfect centralizer2A := by
  let : Group.IsPerfect (BinaryFivePointStabilizer.stabilizer TwoA.markedVector) :=
    pointStabilizer_isPerfect
  constructor
  have hh := CentralExtension.ker_sup_commutator_eq_top_of_surjective
    TwoA.pointAction TwoA.pointAction_surjective
  rw [TwoA.pointAction_ker, sup_eq_right.mpr translation_le_commutator] at hh
  exact hh

private def liftCenter (x : center centralizer2A) : P :=
  ⟨⟨x.val.val, translation_fixes_base ⟨x.val, TwoA.translationKernel_selfCentralizing
    (center_le_centralizer (TwoA.translationKernel : Set centralizer2A) x.property)⟩⟩,
    mem_centralizer_singleton_iff.mpr
      (Subtype.ext (mem_centralizer_singleton_iff.mp x.val.property))⟩
private def centerEmbedding (x : center centralizer2A) : center P :=
  ⟨liftCenter x, mem_center_iff.mpr (fun y => by
    apply pointedInclusion_injective
    exact mem_center_iff.mp x.property (pointedInclusion y))⟩
private theorem centerEmbedding_injective : Function.Injective centerEmbedding := by
  intro x y he
  apply Subtype.ext
  exact congrArg (fun z : center P => pointedInclusion z.val) he

private theorem center_image_eq_zpowers_of_card_le_two {F : Type*} [Group F] [Finite F]
    (t : F) (ht : orderOf t = 2)
    (hcard : Nat.card (center (centralizer ({t} : Set F))) ≤ 2) :
    (center (centralizer ({t} : Set F))).map
      (centralizer ({t} : Set F)).subtype = zpowers t := by
  let D := centralizer ({t} : Set F)
  let z : D := ⟨t, mem_centralizer_singleton_iff.mpr rfl⟩
  have hz : z ∈ center D := mem_center_iff.mpr (fun y =>
    Subtype.ext (mem_centralizer_singleton_iff.mp y.property))
  have hle : zpowers t ≤ (center D).map D.subtype :=
    zpowers_le.mpr (mem_map_of_mem D.subtype hz)
  apply (eq_of_le_of_card_ge hle ?_).symm
  rw [card_map_of_injective D.subtype_injective, Nat.card_zpowers, ht]
  exact hcard

/-- The center of the actual 2A centralizer is precisely the marked involution line. -/
theorem twoA_center_image_eq_zpowers :
    (center centralizer2A).map centralizer2A.subtype = zpowers involution2A := by
  apply center_image_eq_zpowers_of_card_le_two involution2A involution2A_order
  exact (Nat.card_le_card_of_injective centerEmbedding centerEmbedding_injective).trans
    pointed_center_card.le

/-- The marked center has order two. -/
theorem twoA_center_card : Nat.card (center centralizer2A) = 2 := by
  rw [← card_map_of_injective centralizer2A.subtype_injective,
    twoA_center_image_eq_zpowers, Nat.card_zpowers, involution2A_order]

/-- The supplied two-central hypothesis selects 2A; no assertion about 2B is needed. -/
theorem centralizer_equiv_twoA {t : M24} (ht : orderOf t = 2)
    (hc : Theory.GroupTheory.DoubleCoverCentralizer.TwoCentral t) :
    Nonempty (centralizer ({t} : Set M24) ≃* centralizer2A) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_twoA_of_twoCentral t ht hc).symm
  exact ⟨(Theory.GroupTheory.CentralizerSmallKernelTransport.centralizerEquiv
    (MulAut.conj g) t).trans (MulEquiv.subgroupCongr (congrArg
      (fun x : M24 => centralizer ({x} : Set M24)) hg))⟩

/-- Every two-central involution has a perfect full centralizer. -/
theorem isPerfect_of_twoCentral {t : M24} (ht : orderOf t = 2)
    (hc : Theory.GroupTheory.DoubleCoverCentralizer.TwoCentral t) :
    Group.IsPerfect (centralizer ({t} : Set M24)) := by
  obtain ⟨e⟩ := centralizer_equiv_twoA ht hc
  let : Group.IsPerfect centralizer2A := twoA_isPerfect
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

/-- Fusion preserves the order of the original marked center. -/
theorem center_card_of_twoCentral {t : M24} (ht : orderOf t = 2)
    (hc : Theory.GroupTheory.DoubleCoverCentralizer.TwoCentral t) :
    Nat.card (center (centralizer ({t} : Set M24))) = 2 := by
  obtain ⟨e⟩ := centralizer_equiv_twoA ht hc
  exact (Nat.card_congr (centerCongr e).toEquiv).trans twoA_center_card

/-- The ambient center image is the line of the original two-central involution. -/
theorem center_image_eq_zpowers {t : M24} (ht : orderOf t = 2)
    (hc : Theory.GroupTheory.DoubleCoverCentralizer.TwoCentral t) :
    (center (centralizer ({t} : Set M24))).map
      (centralizer ({t} : Set M24)).subtype = zpowers t :=
  center_image_eq_zpowers_of_card_le_two t ht (center_card_of_twoCentral ht hc).le

/-- Preserving the center line fixes the marked involution. -/
theorem self_normalizing_of_twoCentral {t : M24} (ht : orderOf t = 2)
    (hc : Theory.GroupTheory.DoubleCoverCentralizer.TwoCentral t) :
    normalizer (centralizer ({t} : Set M24) : Set M24) = centralizer ({t} : Set M24) := by
  apply le_antisymm
  · exact normalizer_le_centralizer_of_characteristic_involution
      (centralizer ({t} : Set M24)) (center _) t ht (center_image_eq_zpowers ht hc)
  · exact le_normalizer

/-- The exact residual-control input for the original M₂₄ source row. -/
theorem centralizer_eq_of_residual_le (U : Subgroup M24) (t : M24)
    (ht : orderOf t = 2)
    (hc : Theory.GroupTheory.DoubleCoverCentralizer.TwoCentral t)
    (hCU : centralizer ({t} : Set M24) ≤ U)
    (hR : (solvableResidual U).map U.subtype ≤ centralizer ({t} : Set M24)) :
    U = centralizer ({t} : Set M24) := by
  let D := centralizer ({t} : Set M24)
  let : Group.IsPerfect D := isPerfect_of_twoCentral ht hc
  have he : (solvableResidual U).map U.subtype = D :=
    le_antisymm hR (le_map_solvableResidual_of_isPerfect D U hCU)
  have hn : U ≤ normalizer (D : Set M24) := by
    rw [← he]
    have hh := (solvableResidual U).le_normalizer_map U.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hh
  rw [self_normalizing_of_twoCentral ht hc] at hn
  exact le_antisymm hn hCU
end OrdinarySource
end Sporadic.Mathieu.M24InvolutionCentralizers
