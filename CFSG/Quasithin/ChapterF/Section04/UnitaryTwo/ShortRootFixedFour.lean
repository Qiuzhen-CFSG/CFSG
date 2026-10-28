module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourShortRoot.RadicalFixed
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.PlainFusion
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourFieldCoordinates
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourPointResidual
public import Theory.GroupTheory.PGroup.CyclicInvolution
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# The fixed-four obstruction in the marked U₄(2) completion

The literal plane embedding carries the cubic-fixed radical to a four-group
containing a conjugate of the marked long root. Any four-subgroup of the
source plane core centralized by this cubic is the whole fixed four-group.
The original long-root centralizer bound puts its centralizing subgroups
inside a conjugate of the solvable point endpoint.

This is the adequate final exceptional-row argument in Aschbacher–Smith
F.4.42, printed pp.295–296. The earlier recognition argument must still
produce the indicated four-group and its centralizing A₅. The cubic fixed
space is used here; it is not replaced by the smaller full-S₃ fixed space.
-/

@[expose] public noncomputable section
open Subgroup Theory.SpecificGroups.ClassicalUnitary
namespace CFSG.Quasithin.ChapterF.UnitaryTwo.ShortRootFixedFour
open GreenBook.LieModels.UnitaryFour
open UnitaryFourFlag UnitaryFourPlaneRadical UnitaryFourShortRoot
local notation "hn" => Nat.le_refl 1
local notation "F" => MatrixField 1
local notation "σ" => fieldConj 1
local notation "hσ" => fieldConj_involutive 1 hn
local notation "L" => L2Matrix 1 hn
local notation "P" => pointParabolic 1 hn

/-- The binary field supplies the required trace-one and norm-one parameter. -/
theorem exists_long_fixed_parameter : ∃ b : F, b + σ b = 1 ∧ b * σ b = 1 := by
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨b, hb⟩ := (FieldCoordinates.exists_trace_iff 1 hn 1).mpr (map_one _)
  change b + σ b = 1 at hb
  have hb0 : b ≠ 0 := by intro he; simp [he] at hb
  have hc : σ b = b ^ 2 := by rw [fieldConj_apply]; norm_num
  have hpow : b ^ 3 = 1 := by
    have ht := FiniteField.pow_card_sub_one_eq_one b hb0
    have hf : Nat.card F = 4 := by simpa using matrixField_card 1 hn
    simpa [← Nat.card_eq_fintype_card, hf] using ht
  refine ⟨b, hb, ?_⟩
  rw [hc, ← pow_succ']
  exact hpow

/-- The full first endpoint is solvable in the binary model. -/
theorem point_isSolvable : Group.IsSolvable P := by
  let J := standardForm 1 hn
  let f := inclusion (UnitaryFourPointLocal.localSU_le_pointParabolicSU F J)
  let g := UnitaryFourPointResidual.pointScalarUnits F J
  let : Group.IsSolvable (UnitaryFourPointLocal.localSU F J) :=
    PointLocal.matrixLocal_isSolvable_two
  have hk : g.ker ≤ f.range := by
    rw [UnitaryFourPointResidual.pointScalarUnits_ker]
    intro x hx
    exact ⟨⟨x.val, hx⟩, rfl⟩
  let : Group.IsSolvable (pointParabolicMatrix 1 hn) :=
    Group.isSolvable_of_ker_le_range f g hk
  let e : pointParabolicMatrix 1 hn ≃* P :=
    (pointParabolicMatrix 1 hn).equivMapOfInjective (projection 1 hn) (projection_injective 1 hn)
  exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective

theorem long_mem_point :
    (longLocal F σ hσ).val ∈ pointParabolicMatrix 1 hn := by
  change (longLocal F σ hσ).val ∈ pointParabolicSU F (form F σ hσ)
  rw [mem_pointParabolicSU]
  exact ⟨rfl, rfl, rfl⟩

/-- The same marked long root, viewed in the first endpoint. -/
def longPoint : P :=
  ⟨projection 1 hn (longLocal F σ hσ).val, ⟨_, long_mem_point, rfl⟩⟩

/-- The chosen matrix is the nonidentity element of the original marked
center of the first endpoint's two-core. -/
theorem longPoint_mem_root : longPoint ∈ PointCore.rootSubgroup := by
  let R := UnitaryFourPointLocal.radical F σ hσ
  let Q := UnitaryFourConverse.PointParabolic.parabolicRadical F σ hσ
  let a : center R :=
    (UnitaryFourPointLocal.centerEquivFixedField F σ hσ
      (PointLocal.fieldConj_nontrivial 1 hn)).symm (Multiplicative.ofAdd 1)
  let j := inclusion (UnitaryFourPointLocal.localSU_le_pointParabolicSU F (standardForm 1 hn))
  let e : R ≃* Q := R.equivMapOfInjective j (inclusion_injective _)
  let Z := (center Q).map Q.subtype
  have hZ : Z ≤ center (pointParabolicMatrix 1 hn) := by
    let : Z.Normal := ConjAct.normal_of_characteristic_of_normal
    exact central_of_normal_card_two Z
      ((card_map_of_injective Q.subtype_injective).trans PointCore.radical_center_card_two)
  let v : pointParabolicMatrix 1 hn := (e a.val).val
  have hvZ : v ∈ Z := ⟨e a.val, (centerCongr e a).property, rfl⟩
  have hvO : v ∈ pCore 2 (pointParabolicMatrix 1 hn) :=
    UnitaryFourConverse.PointParabolic.parabolicRadical_le_twoCore F σ hσ (e a.val).property
  let o : pCore 2 (pointParabolicMatrix 1 hn) := ⟨v, hvO⟩
  have ho : o ∈ center (pCore 2 (pointParabolicMatrix 1 hn)) :=
    mem_center_iff.mpr fun w => Subtype.ext (mem_center_iff.mp (hZ hvZ) w.val)
  let ep : pointParabolicMatrix 1 hn ≃* P :=
    (pointParabolicMatrix 1 hn).equivMapOfInjective (projection 1 hn) (projection_injective 1 hn)
  let eo : pCore 2 (pointParabolicMatrix 1 hn) ≃* pCore 2 P :=
    (ep.subgroupMap _).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 ep))
  refine ⟨eo o, (centerCongr eo ⟨o, ho⟩).property, ?_⟩
  apply Subtype.ext
  apply congrArg (projection 1 hn)
  apply Subtype.ext
  apply Units.ext
  change UnitaryFourPointLocal.radicalMatrix F σ ⟨0,0,1, _⟩ =
    unipotentMatrix F (longParameter F σ).val
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [UnitaryFourPointLocal.radicalMatrix, unipotentMatrix, longParameter]

theorem longPoint_order : orderOf longPoint = 2 := by
  have hs : (longLocal F σ hσ).val ^ 2 = 1 := by
    apply Subtype.ext
    apply Units.ext
    change (unipotentMatrix F (longParameter F σ).val) ^ 2 = 1
    rw [pow_two, ← unipotentMatrix_add]
    have he : (longParameter F σ).val + (longParameter F σ).val = 0 := by
      ext r s
      exact CharTwo.add_self_eq_zero _
    rw [he, unipotentMatrix_zero]
  apply orderOf_eq_prime_iff.mpr
  constructor
  · apply Subtype.ext
    exact (map_pow (projection 1 hn) (longLocal F σ hσ).val 2).symm.trans
      ((congrArg (projection 1 hn) hs).trans (map_one _))
  · intro he
    have he0 : projection 1 hn (longLocal F σ hσ).val = projection 1 hn 1 := by
      exact (congrArg Subtype.val he).trans (map_one _).symm
    have he' := (projection_injective 1 hn) he0
    have h := congrArg (fun g : MatrixGroup 1 hn => g.val.val 0 3) he'
    exact one_ne_zero h

/-- The source's arbitrary nonidentity marked root is this explicit matrix. -/
theorem root_eq_longPoint (z : P) (hz : orderOf z = 2) (hr : z ∈ PointCore.rootSubgroup) :
    z = longPoint := by
  let : IsCyclic PointCore.rootSubgroup := isCyclic_of_prime_card PointCore.rootSubgroup_card
  have ha : orderOf (⟨z, hr⟩ : PointCore.rootSubgroup) = 2 :=
    (orderOf_injective PointCore.rootSubgroup.subtype Subtype.val_injective _).symm.trans hz
  have hb : orderOf (⟨longPoint, longPoint_mem_root⟩ : PointCore.rootSubgroup) = 2 :=
    (orderOf_injective PointCore.rootSubgroup.subtype Subtype.val_injective _).symm.trans longPoint_order
  exact congrArg Subtype.val (IsCyclic.eq_of_orderOf_eq_two ha hb)

private def longOverlap : overlap 1 hn :=
  ⟨longPoint.val, by
    rw [← exact_overlap]
    exact ⟨longPoint.property, L2_le_planeParabolic 1 hn
      (L2ProjectIso 1 hn (longLocal F σ hσ)).property⟩⟩

variable {G G0 : Type*} [Group G] [Group G0]
variable (c : Theory.GroupTheory.RankTwoAmalgam.FaithfulCompletion
  (amalgam 1 hn) (G := G0)) (i : G0 →* G)

/-- The actual matrix plane factor maps through the original right endpoint. -/
def matrixPlaneEmbedding : L2Matrix 1 hn →* G :=
  (PlainFusion.planeEmbedding c i).comp (L2ProjectIso 1 hn).toMonoidHom

theorem matrixPlaneEmbedding_injective (hi : Function.Injective i) :
    Function.Injective (matrixPlaneEmbedding c i) :=
  (PlainFusion.planeEmbedding_injective c i hi).comp (L2ProjectIso 1 hn).injective

theorem radical_image :
    (radical F σ hσ).map (matrixPlaneEmbedding c i) = PlainFusion.planeImage c i := by
  change (L2MatrixRadical 1 hn).map
    ((PlainFusion.planeEmbedding c i).comp (L2ProjectIso 1 hn).toMonoidHom) = _
  rw [← map_map, L2MatrixRadical_eq_twoCore]
  rw [pCore_map_iso]
  rfl

theorem long_image : matrixPlaneEmbedding c i (longLocal F σ hσ) = i (c.left longPoint) :=
  (congrArg i (DFunLike.congr_fun c.compatible longOverlap)).symm

/-- A group centralizing the exceptional fixed four-group is solvable,
using the original marked long-root centralizer bound. -/
theorem source_fixed_four_centralizer_isSolvable
    (hi : Function.Injective i)
    (hc : centralizer ({i (c.left longPoint)} : Set G) ≤ (i.comp c.left).range)
    (E : Subgroup G) (hEQ : E ≤ PlainFusion.sourcePlaneRootImage c i)
    (hEc : E ≤ centralizer
      ({matrixPlaneEmbedding c i (levi F σ hσ (cubic F))} : Set G))
    (hE : Nat.card E = 4)
    (A : Subgroup G) (hA : A ≤ centralizer (E : Set G)) : Group.IsSolvable A := by
  have hsol : Group.IsSolvable (centralizer
      ({matrixPlaneEmbedding c i (longLocal F σ hσ)} : Set G)) := by
    rw [long_image]
    let : Group.IsSolvable P := point_isSolvable
    let : Group.IsSolvable (i.comp c.left).range :=
      Group.isSolvable_of_surjective (f := (i.comp c.left).rangeRestrict)
        (i.comp c.left).rangeRestrict_surjective
    exact Group.isSolvable_of_isSolvable_injective (f := inclusion hc) (inclusion_injective hc)
  obtain ⟨b, ht, hn'⟩ := exists_long_fixed_parameter
  apply centralizing_fixed_order_subgroup_isSolvable F σ hσ
    (matrixPlaneEmbedding c i) (matrixPlaneEmbedding_injective c i hi)
    E ?_ hEc ?_ b ht hn' hsol A hA
  · change E ≤ (radical F σ hσ).map (matrixPlaneEmbedding c i)
    rw [radical_image, ← PlainFusion.sourcePlaneRootImage_eq]
    exact hEQ
  · rw [matrixField_card 1 hn]
    exact hE

/-- The A₅ factor in the exceptional normalizer row cannot centralize the
original four-subgroup of the plane core fixed by the marked cubic. -/
theorem source_no_alternating_five_centralizing_fixed_four
    (hi : Function.Injective i)
    (hc : centralizer ({i (c.left longPoint)} : Set G) ≤ (i.comp c.left).range)
    (E : Subgroup G) (hEQ : E ≤ PlainFusion.sourcePlaneRootImage c i)
    (hEc : E ≤ centralizer
      ({matrixPlaneEmbedding c i (levi F σ hσ (cubic F))} : Set G))
    (hE : Nat.card E = 4) (A : Subgroup G)
    (hA : A ≤ centralizer (E : Set G)) :
    ¬ Nonempty (A ≃* alternatingGroup (Fin 5)) := by
  rintro ⟨e⟩
  let : Group.IsSolvable A :=
    source_fixed_four_centralizer_isSolvable c i hi hc E hEQ hEc hE A hA
  let : Group.IsSolvable (alternatingGroup (Fin 5)) :=
    Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 5)) inferInstance

/-- Literal marked-source application, retaining the original arbitrary
long-root involution and its original centralizer hypothesis. -/
theorem source_fixed_four_obstruction
    (hi : Function.Injective i) (z : pointParabolic 1 hn)
    (hz : orderOf z = 2) (hr : z ∈ PointCore.rootSubgroup)
    (hc : centralizer ({i (c.left z)} : Set G) ≤ (i.comp c.left).range)
    (E : Subgroup G) (hEQ : E ≤ PlainFusion.sourcePlaneRootImage c i)
    (hEc : E ≤ centralizer
      ({matrixPlaneEmbedding c i (levi F σ hσ (cubic F))} : Set G))
    (hE : Nat.card E = 4) (A : Subgroup G)
    (hA : A ≤ centralizer (E : Set G))
    (hmodel : Nonempty (A ≃* alternatingGroup (Fin 5))) : False := by
  have hmark := root_eq_longPoint z hz hr
  rw [hmark] at hc
  exact source_no_alternating_five_centralizing_fixed_four c i hi hc E hEQ hEc hE A hA hmodel

end CFSG.Quasithin.ChapterF.UnitaryTwo.ShortRootFixedFour
