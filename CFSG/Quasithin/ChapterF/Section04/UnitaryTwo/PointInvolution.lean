module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointShear
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.ModelFusion
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.PointResidual
public import Theory.GroupTheory.QuaternionCentralProductResidualSwap
public import Theory.GroupTheory.ConjugatePairSeed.OrthogonalAction
public import Theory.GroupTheory.NormalizingInvolutionCard

/-!
# The marked involution of the binary unitary point parabolic

The middle shear lies in the literal plane radical and outside the point
core. Its square-one displacements exchange the quaternion factors and
hence the residual SL2(3) factors. It complements the two-residual in the
whole point group. Its fixed point core has order eight; joining the shear
recovers the marked plane radical of order sixteen. That module's normalizer
is the exact flag overlap.

The matrix calculation is in UnitaryFourPointShear; the core and residual
are the actual groups constructed in PointQuaternion and PointResidual.
These discharge the model packet for Aschbacher--Smith 13.5.17, ordinary
U4(2) branch, printed p.922, with local geometry from F.4.27 and F.4.29.
-/

@[expose] public noncomputable section
open Matrix Subgroup BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.UnitaryTwo.PointInvolution
open GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag
local notation "hn" => Nat.le_refl 1
local notation "F" => MatrixField 1
local notation "σ" => fieldConj 1
local notation "hσ" => fieldConj_involutive 1 hn
local notation "MP" => pointParabolicSU F (form F σ hσ)
local notation "P" => pointParabolic 1 hn
local notation "M" => ProjectiveGroup 1 hn

/-- The faithful map used by both literal point endpoints. -/
def matrixPointEquiv : MP ≃* P :=
  (MP).equivMapOfInjective (projection 1 hn) (projection_injective 1 hn)

/-- The middle shear, in the actual projective point parabolic. -/
def involution : P := matrixPointEquiv (UnitaryFourPointShear.element F σ hσ)

/-- The marked plane radical, restricted to the point endpoint. -/
def pointModule : Subgroup P := InvolutionPlacement.planeCore.subgroupOf P

theorem planeCore_le_point : InvolutionPlacement.planeCore ≤ P := by
  rw [← InvolutionPlacement.matrix_plane_core_map]
  change ((pCore 2 (L2Matrix 1 hn)).map (L2Matrix 1 hn).subtype).map
    (projection 1 hn) ≤ (MP).map (projection 1 hn)
  apply map_mono
  rw [← L2MatrixRadical_eq_twoCore]
  exact UnitaryFourPointShear.planeRadical_le_point F σ hσ

instance pointModule_elementary : IsElementaryAbelian 2 pointModule := by
  let : IsElementaryAbelian 2 InvolutionPlacement.planeCore :=
    IsElementaryAbelian.map (L2 1 hn).subtype
  exact IsElementaryAbelian.subgroupOf planeCore_le_point

theorem pointModule_card : Nat.card pointModule = 16 := by
  rw [pointModule,Nat.card_congr (subgroupOfEquivOfLe planeCore_le_point).toEquiv]
  rw [InvolutionPlacement.planeCore,card_map_of_injective (L2 1 hn).subtype_injective,
    L2TwoCore_card]
  norm_num

/-- Its normalizer inside the point endpoint is the exact flag overlap. -/
theorem pointModule_normalizer : normalizer (pointModule : Set P) =
    (overlap 1 hn).subgroupOf P := by
  rw [pointModule,← subgroupOf_normalizer_eq planeCore_le_point,
    ModelFusion.planeCore_normalizer]
  ext x
  change (x : M) ∈ planeParabolic 1 hn ↔ (x : M) ∈ overlap 1 hn
  rw [← exact_overlap]
  exact ⟨fun h => ⟨x.property,h⟩,fun h => h.2⟩

theorem involution_sq : involution^2=1 := by
  exact (map_pow matrixPointEquiv _ 2).symm.trans
    ((congrArg matrixPointEquiv (UnitaryFourPointShear.element_sq F σ hσ)).trans matrixPointEquiv.map_one)

theorem involution_mem_module : involution ∈ pointModule := by
  change projection 1 hn (UnitaryFourPointShear.element F σ hσ).val ∈
    InvolutionPlacement.planeCore
  rw [← InvolutionPlacement.matrix_plane_core_map]
  apply mem_map_of_mem
  rw [← L2MatrixRadical_eq_twoCore]
  exact UnitaryFourPointShear.element_mem_planeRadical F σ hσ

theorem involution_not_mem_core : involution ∉ pCore 2 P := by
  rw [← pCore_map_iso 2 matrixPointEquiv]
  intro h
  have hm := (mem_map_iff_mem matrixPointEquiv.injective).mp h
  rw [← PointQuaternion.parabolic_radical_eq_core] at hm
  exact UnitaryFourPointShear.element_not_mem_radical F σ hσ hm

private theorem radical_lift (x : pCore 2 P) :
    ∃ r : UnitaryFourPointLocal.radical F σ hσ,
      projection 1 hn r.val.val = (x : P).val := by
  have hm : (x : P) ∈ (pCore 2 MP).map matrixPointEquiv.toMonoidHom := by
    rw [pCore_map_iso]
    exact x.property
  obtain ⟨y,hy,he⟩ := hm
  rw [← PointQuaternion.parabolic_radical_eq_core] at hy
  obtain ⟨r,hr,hry⟩ := hy
  exact ⟨⟨r,hr⟩, (congrArg (fun z : MP => projection 1 hn z.val) hry).trans
    (congrArg Subtype.val he)⟩

private theorem involution_singular : BinaryFourPlus.SingularDisplacements
    (PointQuaternion.projectivePointQuaternionData.quotientWreathAction
      (MulAut.conjNormal involution)) := by
  apply PointQuaternion.projectivePointQuaternionData.wreath_singular_displacement
  intro x
  apply Subtype.ext
  apply Subtype.ext
  obtain ⟨r,hr⟩ := radical_lift x
  change (((involution : P).val * (x : P).val * (involution : P).val⁻¹) *
    (x : P).val⁻¹)^2=1
  rw [←hr]
  change ((project F (form F σ hσ) (UnitaryFourPointShear.element F σ hσ).val *
    project F (form F σ hσ) r.val.val *
    (project F (form F σ hσ) (UnitaryFourPointShear.element F σ hσ).val)⁻¹) *
    (project F (form F σ hσ) r.val.val)⁻¹)^2=1
  have hh := congrArg (project F (form F σ hσ))
    (UnitaryFourPointShear.displacement_sq F σ hσ r)
  simp only [map_pow,map_mul,map_inv,map_one] at hh
  exact hh

theorem involution_swaps_residual :
    PointResidual.projectivePointResidualData.left.map (MulAut.conj involution).toMonoidHom =
      PointResidual.projectivePointResidualData.right ∧
    PointResidual.projectivePointResidualData.right.map (MulAut.conj involution).toMonoidHom =
      PointResidual.projectivePointResidualData.left :=
  PointResidual.projectivePointResidualData.swap_factors_of_singular_actor involution
    involution_singular PointCore.projective_point_core_selfCentralizing involution_not_mem_core

private theorem fixed_core_le_module :
    pCore 2 P ⊓ centralizer ({involution} : Set P) ≤ pointModule := by
  intro x hx
  obtain ⟨r,hr⟩ := radical_lift ⟨x,hx.1⟩
  have hc : Commute (UnitaryFourPointShear.element F σ hσ).val r.val.val := by
    apply (project_injective F (form F σ hσ))
    rw [map_mul,map_mul]
    change projection 1 hn (UnitaryFourPointShear.element F σ hσ).val * projection 1 hn r.val.val =
      projection 1 hn r.val.val * projection 1 hn (UnitaryFourPointShear.element F σ hσ).val
    rw [hr]
    exact (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hx.2)).symm
  change x.val ∈ InvolutionPlacement.planeCore
  rw [←hr,← InvolutionPlacement.matrix_plane_core_map]
  apply mem_map_of_mem
  rw [← L2MatrixRadical_eq_twoCore]
  exact UnitaryFourPointShear.fixed_radical_mem_plane F σ hσ r hc

/-- The chosen shear recovers the entire original plane module intrinsically. -/
theorem pointModule_from_involution : pointModule =
    (pCore 2 P ⊓ centralizer ({involution} : Set P)) ⊔ zpowers involution := by
  have h8 := PointQuaternion.projectivePointQuaternionData.fixed_core_card_of_singular_involution
    (pCore 2 P) involution involution_sq involution_singular
    PointCore.projective_point_core_selfCentralizing involution_not_mem_core
  have hnormFixed : involution ∈ normalizer
      (pCore 2 P ⊓ centralizer ({involution} : Set P) : Subgroup P) := by
    apply Subgroup.centralizer_le_normalizer
    intro x hx
    exact mem_centralizer_singleton_iff.mp hx.2
  symm
  apply eq_of_le_of_card_ge (sup_le fixed_core_le_module (zpowers_le.mpr involution_mem_module))
  have hout : involution ∉ pCore 2 P ⊓ centralizer ({involution} : Set P) :=
    fun h => involution_not_mem_core h.1
  rw [card_sup_zpowers_of_normalizing_involution _ _ involution_sq
    hout hnormFixed,h8,pointModule_card]

/-- The same marked shear splits the full point group over its two-residual. -/
theorem involution_complement : (pResidual 2 P).IsComplement' (zpowers involution) := by
  let q := PointQuaternion.projectivePointQuaternionData
  let c := PointResidual.projectivePointResidualData
  have hvr : involution ∉ pResidual 2 P := by
    intro h
    have hp : IsPGroup 2 pointModule := IsElementaryAbelian.isPGroup 2 pointModule
    exact involution_not_mem_core (q.residual_inf_two_subgroup_le _ c pointModule hp
      ⟨h,involution_mem_module⟩)
  have hnorm : involution ∈ normalizer (pResidual 2 P : Set P) := by
    rw [(pResidual 2 P).normalizer_eq_top]
    trivial
  have htop : pResidual 2 P ⊔ zpowers involution = ⊤ := by
    apply eq_of_le_of_card_ge le_top
    rw [card_sup_zpowers_of_normalizing_involution _ _ involution_sq hvr hnorm,
      q.residual_card _ c,Nat.card_congr topEquiv.toEquiv,BinaryCompletion.point_card]
  have hd := (pResidual 2 P).disjoint_zpowers_of_prime_order_not_mem involution
    (orderOf_eq_prime involution_sq (fun he => hvr (he ▸ (pResidual 2 P).one_mem))) hvr
  apply isComplement'_of_disjoint_and_mul_eq_univ hd
  rw [← Subgroup.normal_mul,htop]
  rfl

end CFSG.Quasithin.ChapterF.UnitaryTwo.PointInvolution
