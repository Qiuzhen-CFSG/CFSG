module

public import Theory.SpecificGroups.Monster.Construction.LocalC.SourceNormalizer
public import Theory.SpecificGroups.Monster.Construction.LocalC.LeechOrientation
public import Theory.SpecificGroups.Monster.Construction.LocalC.TensorKernel

/-!
# The determinant-one source construction of the local group

Section 27 takes the spin normalizer inside SL and the determinant-one Leech
isometries, matches their actions on the binary Leech space, and takes the
tensor image. The proved normalizer comparison and Leech orientation identify
these factors with the factors of `localPullback`. The resulting isomorphism
preserves both linear maps, so its tensor image is exactly the existing `C`.

Matching over the full binary orthogonal space already restricts the spin
factor to the inverse image of the Leech binary action, which is the source's
`C₁`. No order or simplicity assertion about a Conway group enters this
identification. All maps use the fixed source Golay–Leech comparison.

Source: Aschbacher, *Sporadic Groups*, Section 27, printed pp. 147–149.
-/

@[expose] public section
noncomputable section
open scoped TensorProduct
open Atlas.Lattices
namespace Sporadic.Monster.Construction.LocalC
open TrialitySpin SourceNormalizer

/-- The determinant-one subgroup of the actual Leech isometry group. -/
def sourceLeechIsometries : Subgroup LeechIsometryGroup :=
  (LinearEquiv.det.comp realLeechRepresentation).ker

@[simp] theorem mem_sourceLeechIsometries (g : LeechIsometryGroup) :
    g ∈ sourceLeechIsometries ↔ LinearMap.det (realLeechRepresentation g).toLinearMap = 1 := by
  change LinearEquiv.det (realLeechRepresentation g) = 1 ↔ _
  rw [← Units.val_inj]
  simp only [LinearEquiv.coe_det, Units.val_one]

theorem sourceLeechIsometries_eq_top : sourceLeechIsometries = ⊤ := by
  apply top_unique
  intro g _
  exact (mem_sourceLeechIsometries g).mpr (realLeechRepresentation_det g)

/-- Every actual Leech isometry belongs to the source determinant-one factor. -/
def leechEquivSourceLeechIsometries : LeechIsometryGroup ≃* sourceLeechIsometries where
  toFun g := ⟨g, (mem_sourceLeechIsometries g).mpr (realLeechRepresentation_det g)⟩
  invFun := Subtype.val
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem leechEquivSourceLeechIsometries_val (g : LeechIsometryGroup) :
    (leechEquivSourceLeechIsometries g).val = g := rfl

/-- The automorphism induced by the source SL normalizer on the faithful spin subgroup. -/
def sourceSpinAutomorphism : sourceSLNormalizer →* MulAut Q1Image :=
  (MonoidHom.snd _ _).comp (spinNormalizer.subtype.comp sourceSLNormalizerLift)

/-- The automorphism is literal conjugation, transported along the faithful spin map. -/
theorem sourceSpinAutomorphism_eq_induced (F : sourceSLNormalizer) :
    sourceSpinAutomorphism F = inducedAutomorphism F.val F.prop.1 := by
  apply ((normalizes_iff_existsUnique F.val).mp F.prop.1).unique
  · intro q v
    have h := (sourceSLNormalizerLift F).prop.1 q v
    change spinProjection (sourceSLNormalizerLift F) (SpinAction.imageRepresentation q v) =
      SpinAction.imageRepresentation (sourceSpinAutomorphism F q)
        (spinProjection (sourceSLNormalizerLift F) v) at h
    simpa only [spinProjection_sourceSLNormalizerLift] using h
  · exact inducedAutomorphism_intertwines F.val F.prop.1

@[simp] theorem sourceSpinAutomorphism_equiv (f : spinNormalizer) :
    sourceSpinAutomorphism (spinNormalizerEquivSourceSLNormalizer f) = f.val.2 := by
  change (spinNormalizerEquivSourceSLNormalizer.symm
    (spinNormalizerEquivSourceSLNormalizer f)).val.2 = f.val.2
  rw [spinNormalizerEquivSourceSLNormalizer.symm_apply_apply]

/-- The two actual actions to be matched on the binary Leech space. -/
def sourceLeechProjection : sourceSLNormalizer × sourceLeechIsometries →*
    MulAut Q1Image × LeechIsometryGroup :=
  sourceSpinAutomorphism.prodMap sourceLeechIsometries.subtype

/-- The source fiber product, with the spin factor automatically restricted to
those binary actions realized by Leech isometries. -/
def sourcePullback : Subgroup (sourceSLNormalizer × sourceLeechIsometries) :=
  (compatibleAutomorphisms sourceLatticeComparison).comap sourceLeechProjection

/-- Membership uses the actual induced conjugation and the fixed source comparison. -/
theorem mem_sourcePullback (p : sourceSLNormalizer × sourceLeechIsometries) :
    p ∈ sourcePullback ↔ ∀ q : Q1Image,
      latticeClass sourceLatticeComparison (inducedAutomorphism p.1.val p.1.prop.1 q) =
        leechModTwoRepresentation p.2.val (latticeClass sourceLatticeComparison q) := by
  change (∀ q, latticeClass sourceLatticeComparison (sourceSpinAutomorphism p.1 q) =
    leechModTwoRepresentation p.2.val (latticeClass sourceLatticeComparison q)) ↔ _
  rw [sourceSpinAutomorphism_eq_induced]

/-- The graph pullback identifies with the source determinant-one fiber product. -/
def localPullbackEquivSource : localPullback ≃* sourcePullback where
  toFun p := ⟨(spinNormalizerEquivSourceSLNormalizer p.val.1,
    leechEquivSourceLeechIsometries p.val.2), by
      have hp : ∀ q, latticeClass sourceLatticeComparison (p.val.1.val.2 q) =
        leechModTwoRepresentation p.val.2 (latticeClass sourceLatticeComparison q) := p.prop
      change ∀ q, latticeClass sourceLatticeComparison
        (sourceSpinAutomorphism (spinNormalizerEquivSourceSLNormalizer p.val.1) q) =
        leechModTwoRepresentation p.val.2 (latticeClass sourceLatticeComparison q)
      simpa only [sourceSpinAutomorphism_equiv] using hp⟩
  invFun p := ⟨(sourceSLNormalizerLift p.val.1, p.val.2.val), p.prop⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact spinNormalizerEquivSourceSLNormalizer.symm_apply_apply p.val.1
    · rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact spinNormalizerEquivSourceSLNormalizer.apply_symm_apply p.val.1
    · rfl
  map_mul' p q := by
    apply Subtype.ext
    apply Prod.ext
    · exact map_mul spinNormalizerEquivSourceSLNormalizer p.val.1 q.val.1
    · rfl

@[simp] theorem localPullbackEquivSource_spin (p : localPullback) :
    (localPullbackEquivSource p).val.1.val = p.val.1.val.1 := rfl

@[simp] theorem localPullbackEquivSource_leech (p : localPullback) :
    (localPullbackEquivSource p).val.2.val = p.val.2 := rfl

/-- The source tensor map uses the actual linear maps of its two factors. -/
def sourceTensor : sourcePullback →* (MinusSpace ≃ₗ[ℝ] MinusSpace) where
  toFun p := TensorProduct.congr (realLeechRepresentation p.val.2.val) p.val.1.val
  map_one' := by
    apply LinearEquiv.toLinearMap_injective
    apply TensorProduct.ext'
    intro v w
    simp
  map_mul' p q := by
    apply LinearEquiv.toLinearMap_injective
    apply TensorProduct.ext'
    intro v w
    simp

@[simp] theorem sourceTensor_tmul (p : sourcePullback) (a : NaturalSpace) (b : SpinSpace) :
    sourceTensor p (a ⊗ₜ[ℝ] b) =
      realLeechRepresentation p.val.2.val a ⊗ₜ[ℝ] p.val.1.val b := rfl

@[simp] theorem sourceTensor_equiv (p : localPullback) :
    sourceTensor (localPullbackEquivSource p) = pullbackTensor p := rfl

/-- The existing local group is exactly the tensor image of the source SL construction. -/
theorem sourceTensor_range_eq_C : sourceTensor.range = C := by
  apply le_antisymm
  · rintro F ⟨p, rfl⟩
    obtain ⟨q, rfl⟩ := localPullbackEquivSource.surjective p
    exact ⟨q, (sourceTensor_equiv q).symm⟩
  · rintro F ⟨p, rfl⟩
    exact ⟨localPullbackEquivSource p, sourceTensor_equiv p⟩

/-- A source description of membership in `C`, without an assumed form law or
an arbitrary lattice comparison. -/
theorem mem_C_iff_source (T : MinusSpace ≃ₗ[ℝ] MinusSpace) : T ∈ C ↔
    ∃ (F : SpinSpace ≃ₗ[ℝ] SpinSpace)
      (hF : F ∈ Subgroup.normalizer (spinLinearGroup : Set _))
      (g : LeechIsometryGroup),
      LinearMap.det F.toLinearMap = 1 ∧
      LinearMap.det (realLeechRepresentation g).toLinearMap = 1 ∧
      (∀ q : Q1Image, latticeClass sourceLatticeComparison (inducedAutomorphism F hF q) =
        leechModTwoRepresentation g (latticeClass sourceLatticeComparison q)) ∧
      TensorProduct.congr (realLeechRepresentation g) F = T := by
  rw [← sourceTensor_range_eq_C]
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨p.val.1.val, p.val.1.prop.1, p.val.2.val,
      ((mem_sourceSLNormalizer _).mp p.val.1.prop).2,
      (mem_sourceLeechIsometries _).mp p.val.2.prop,
      (mem_sourcePullback _).mp p.prop, rfl⟩
  · rintro ⟨F, hF, g, hdet, hgdet, hcompat, hT⟩
    let f : sourceSLNormalizer := ⟨F, (mem_sourceSLNormalizer F).mpr ⟨hF, hdet⟩⟩
    let k : sourceLeechIsometries := ⟨g, (mem_sourceLeechIsometries g).mpr hgdet⟩
    refine ⟨⟨(f,k), (mem_sourcePullback (f,k)).mpr hcompat⟩, hT⟩

/-- The source fiber product maps onto the existing local group by its tensor action. -/
def sourceToC : sourcePullback →* C where
  toFun p := ⟨sourceTensor p, sourceTensor_range_eq_C ▸
    (show sourceTensor p ∈ sourceTensor.range from ⟨p, rfl⟩)⟩
  map_one' := Subtype.ext (map_one sourceTensor)
  map_mul' p q := Subtype.ext (map_mul sourceTensor p q)

@[simp] theorem sourceToC_val (p : sourcePullback) :
    (sourceToC p).val = sourceTensor p := rfl

@[simp] theorem sourceToC_equiv (p : localPullback) :
    sourceToC (localPullbackEquivSource p) = pullbackToC p :=
  Subtype.ext (sourceTensor_equiv p)

theorem sourceToC_surjective : Function.Surjective sourceToC := by
  intro g
  obtain ⟨p, rfl⟩ := pullbackToC_surjective g
  exact ⟨localPullbackEquivSource p, sourceToC_equiv p⟩

/-- The source tensor kernel consists precisely of the paired equal scalar signs. -/
theorem sourceTensor_kernel_iff (p : sourcePullback) : sourceTensor p = 1 ↔
    (p.val.2.val = 1 ∧ ∀ v, p.val.1.val v = v) ∨
      (p.val.2.val = negationIsometry ∧ ∀ v, p.val.1.val v = -v) := by
  obtain ⟨q, rfl⟩ := localPullbackEquivSource.surjective p
  exact pullbackTensor_kernel_iff q

end Sporadic.Monster.Construction.LocalC
