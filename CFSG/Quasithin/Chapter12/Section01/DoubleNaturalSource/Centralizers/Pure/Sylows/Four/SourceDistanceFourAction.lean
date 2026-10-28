module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.SourceCoreAction
public import CFSG.Quasithin.ChapterC.Section01.BlockDefs

/-!
# The literal pure-point residual acts onto its geometric radical

The original residual maps onto the full vector stabilizer with a two-group
kernel. Each geometric radical element is a commutator with its first entry
already in that radical. Consequently the intrinsic commutator core maps onto
the entire radical, retaining the original point and its action.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel
open ChapterC BinaryLinear BinaryLinear.OuterCyclic Theory.LinearAlgebra
open BinaryNaturalDual.VectorStabilizers BinaryNaturalDual.VectorStabilizers.Pure

section Linear
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem transvection_cross (w y : V)
    (α β : V →ₗ[ZMod 2] ZMod 2)
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
private theorem point_kernel_le_core_commutator [FiniteDimensional (ZMod 2) V]
    (hV : 3 ≤ Module.finrank (ZMod 2) V) {v : V} (hv : v ≠ 0) :
    BinaryFivePointStabilizer.kernel v ≤ ⁅BinaryFivePointStabilizer.kernel v, (⊤ : Subgroup (BinaryFivePointStabilizer.stabilizer v))⁆ := by
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
    have hb1 : Module.finrank (ZMod 2) β.range ≤ 1 := by simpa using hb
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
  apply commutator_mem_commutator ?_ (mem_top _)
  apply (BinaryFivePointStabilizer.mem_kernel_iff v a).mpr
  intro z
  change z + α z • v - z ∈ BinaryFivePointStabilizer.line v
  simpa only [add_sub_cancel_left] using
    (Submodule.smul_mem (BinaryFivePointStabilizer.line v) (α z)
      (Submodule.mem_span_singleton_self v))

end Linear

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {B : DoubledBranch T L V 4}
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]
  (S : B.SourceModel)

def distanceFourResidualAction (w : componentOrbit V (T : Subgroup G)) :
    B.pointResidual w →* S.setup.stabilizer (Additive.ofMul w) :=
  (S.pureLocalAction w).comp (inclusion
    (le_inf (B.pointResidual_le_normalizer w) ((B.pointResidual_le w).trans inf_le_right)))

theorem distanceFourResidualAction_surjective
    (w : componentOrbit V (T : Subgroup G)) (hw : w ≠ 1)
    (hp : (B.coordinates w).toAdd.2 = 0) :
    Function.Surjective (S.distanceFourResidualAction w) := by
  intro a
  let u : S.setup.natural := ⟨Additive.ofMul w, (S.natural_marking w).mpr hp⟩
  have ha : a.val ∈ S.setup.residual (Additive.ofMul w) :=
    (S.setup.pure_stabilizer_eq_residual u hw).1 ▸ a.property
  rw [← S.pointResidual_image w] at ha
  obtain ⟨l, hl, he⟩ := ha
  exact ⟨⟨l, mem_map_of_mem _ hl⟩, Subtype.ext he⟩

omit [Finite G] in
theorem distanceFourResidualAction_kernel_two
    (w : componentOrbit V (T : Subgroup G)) :
    IsPGroup 2 (S.distanceFourResidualAction w).ker := by
  let j : B.pointResidual w →* L := inclusion ((B.pointResidual_le w).trans inf_le_left)
  have hj : (S.distanceFourResidualAction w).ker ≤ (pCore 2 L).comap j := by
    intro x hx
    change j x ∈ pCore 2 L
    rw [← B.componentToActionQuotient_ker]
    exact congrArg Subtype.val (show S.distanceFourResidualAction w x = 1 from hx)
  exact (pCore_isPGroup.comap_of_injective j
    (inclusion_injective ((B.pointResidual_le w).trans inf_le_left))).to_le hj

def distanceFourPointVector (w : componentOrbit V (T : Subgroup G))
    (hp : (B.coordinates w).toAdd.2 = 0) : Space 4 :=
  S.setup.naturalCoordinates ⟨Additive.ofMul w, (S.natural_marking w).mpr hp⟩

omit [Finite G] in
theorem distanceFourPointVector_ne_zero
    (w : componentOrbit V (T : Subgroup G)) (hw : w ≠ 1)
    (hp : (B.coordinates w).toAdd.2 = 0) : S.distanceFourPointVector w hp ≠ 0 :=
  S.setup.naturalCoordinates_ne_zero _ hw

def distanceFourPointAction (w : componentOrbit V (T : Subgroup G)) (hw : w ≠ 1)
    (hp : (B.coordinates w).toAdd.2 = 0) :
    B.pointResidual w →* pointStabilizer (S.distanceFourPointVector w hp) :=
  (S.setup.purePointEquiv ⟨Additive.ofMul w, (S.natural_marking w).mpr hp⟩ hw).toMonoidHom.comp
    (S.distanceFourResidualAction w)

theorem distanceFourPointAction_surjective
    (w : componentOrbit V (T : Subgroup G)) (hw : w ≠ 1)
    (hp : (B.coordinates w).toAdd.2 = 0) :
    Function.Surjective (S.distanceFourPointAction w hw hp) :=
  (S.setup.purePointEquiv _ hw).surjective.comp
    (S.distanceFourResidualAction_surjective w hw hp)

theorem distanceFourPointAction_core_image
    (w : componentOrbit V (T : Subgroup G)) (hw : w ≠ 1)
    (hp : (B.coordinates w).toAdd.2 = 0) :
    (pCore 2 (B.pointResidual w)).map (S.distanceFourPointAction w hw hp) =
      pointKernel (S.distanceFourPointVector w hp) := by
  let f := S.distanceFourResidualAction w
  let e := S.setup.purePointEquiv
    (⟨Additive.ofMul w, (S.natural_marking w).mpr hp⟩ : S.setup.natural) hw
  have he : (pCore 2 (B.pointResidual w)).map f =
      pCore 2 (S.setup.stabilizer (Additive.ofMul w)) := by
    rw [← f.comap_pCore_of_ker_isPGroup (S.distanceFourResidualAction_surjective w hw hp)
      (S.distanceFourResidualAction_kernel_two w), map_comap_eq_self_of_surjective
        (S.distanceFourResidualAction_surjective w hw hp)]
  change (pCore 2 (B.pointResidual w)).map (e.toMonoidHom.comp f) = _
  rw [← map_map, he, pCore_map_iso, point_twoCore]
  rfl

theorem distanceFourPointAction_block_image
    (w : componentOrbit V (T : Subgroup G)) (hw : w ≠ 1)
    (hp : (B.coordinates w).toAdd.2 = 0) :
    (blockU (B.pointResidual w)).map (S.distanceFourPointAction w hw hp) =
      pointKernel (S.distanceFourPointVector w hp) := by
  rw [blockU, map_commutator, S.distanceFourPointAction_core_image w hw hp,
    map_top_of_surjective _ (S.distanceFourPointAction_surjective w hw hp)]
  apply le_antisymm (commutator_le_left _ _)
  exact point_kernel_le_core_commutator (by simp [Space])
    (S.distanceFourPointVector_ne_zero w hw hp)

def distanceFourBlockActor (w : componentOrbit V (T : Subgroup G)) (hw : w ≠ 1)
    (hp : (B.coordinates w).toAdd.2 = 0) :
    blockU (B.pointResidual w) →* pointKernel (S.distanceFourPointVector w hp) :=
  ((S.distanceFourPointAction w hw hp).comp (blockU (B.pointResidual w)).subtype).codRestrict _
    (by intro q; rw [← S.distanceFourPointAction_block_image w hw hp];
        exact mem_map_of_mem _ q.property)

theorem distanceFourBlockActor_surjective
    (w : componentOrbit V (T : Subgroup G)) (hw : w ≠ 1)
    (hp : (B.coordinates w).toAdd.2 = 0) :
    Function.Surjective (S.distanceFourBlockActor w hw hp) := by
  rintro ⟨g, hg⟩
  rw [← S.distanceFourPointAction_block_image w hw hp] at hg
  obtain ⟨q, hq, he⟩ := hg
  exact ⟨⟨q, hq⟩, Subtype.ext he⟩

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel
