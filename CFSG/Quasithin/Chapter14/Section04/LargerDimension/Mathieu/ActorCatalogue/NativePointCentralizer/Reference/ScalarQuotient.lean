module
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativePointCentralizer.Reduction

/-!
# Removing the cubic scalars from a binary vector stabilizer

Conjugation on the perfect core's central quotient maps the literal outer
matrix extension onto the native degree-22 design group. The certified matrix
commutant shows that its kernel consists exactly of the three scalar matrices.
Each nonidentity scalar is fixed-point-free on nonzero binary vectors. Thus
restriction to a binary point centralizer is injective. Scalar adjustment then
identifies its quotient image with fixation of the associated three-point orbit.

The final application reduces the reference-vector comparison to an actual
geometric pair-stabilizer calculation. That calculation remains explicit; no
projective stabilizer is substituted for the binary point centralizer.

Source: Aschbacher--Smith, 14.4.12, printed pp.1011--1012, and H.12.1(5,9),
printed pp.393--394 (1 March 2004 manuscript). Original ATLAS matrix attribution
is retained in the imported TwoCoreNormalizer/LinearModel/source directory.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.Native
open Subgroup
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Sporadic.Mathieu
open scoped Pointwise

/-- The faithful degree-22 design action, expressed through actual conjugation. -/
def referenceDesignEquiv : m22DesignAut ≃* MulAut M22 :=
  MulEquiv.ofBijective m22DesignAutToAut
    ⟨m22DesignAutToAut_injective, m22DesignAutToAut_surjective⟩

/-- Projection of the literal outer matrix extension to the native design group. -/
def referenceProjection : Model →* m22DesignAut :=
  referenceDesignEquiv.symm.toMonoidHom.comp
    ((MulAut.congr derivedQuotientEquivM22).toMonoidHom.comp derivedQuotientConjugation)

theorem referenceProjection_surjective : Function.Surjective referenceProjection :=
  referenceDesignEquiv.symm.surjective.comp
    ((MulAut.congr derivedQuotientEquivM22).surjective.comp
      derivedQuotientConjugation_surjective)

/-- The cubic scalar inside the full outer extension. -/
def referenceScalar : Model := componentInclusion M22TripleCover.scalar

theorem referenceScalar_cube : referenceScalar ^ 3 = 1 :=
  Subtype.ext scalarUnit_pow_three

theorem referenceScalar_order : orderOf referenceScalar = 3 :=
  (orderOf_injective componentInclusion (inclusion_injective derivedGroup_le_actionGroup)
    M22TripleCover.scalar).trans M22TripleCover.scalar_order

/-- The kernel will be proved to be precisely this subgroup of scalar matrices. -/
def referenceScalarGroup : Subgroup Model := zpowers referenceScalar

private theorem projection_eq_one_iff (g : Model) :
    referenceProjection g = 1 ↔ derivedConjugation g = 1 := by
  change referenceDesignEquiv.symm
    (MulAut.centralQuotientAction derivedQuotientEquivM22 (derivedConjugation g)) = 1 ↔ _
  rw [map_eq_one_iff _ referenceDesignEquiv.symm.injective,
    map_eq_one_iff _ (MulAut.centralQuotientAction_injective derivedQuotientEquivM22)]

private theorem conjugation_eq_one_cases (g : Model) (hg : derivedConjugation g = 1) :
    g = 1 ∨ g = referenceScalar ∨ g = referenceScalar ^ 2 := by
  have commutes (x : derivedGroup) :
      (g.val : Matrix12) * (x.val : Matrix12) =
        (x.val : Matrix12) * (g.val : Matrix12) := by
    have h := congrArg (fun f : MulAut derivedGroup => (f x).val) hg
    change g.val * x.val * g.val⁻¹ = x.val at h
    exact congrArg Units.val ((mul_inv_eq_iff_eq_mul).mp h)
  have ha : Commute (g.val : Matrix12) matrixA := by
    change (g.val : Matrix12) * matrixA = matrixA * (g.val : Matrix12)
    simpa only [coreGeneratorA, coe_coreA] using commutes coreGeneratorA
  have hb : Commute (g.val : Matrix12) matrixB := by
    change (g.val : Matrix12) * matrixB = matrixB * (g.val : Matrix12)
    simpa only [coreGeneratorB, coe_coreB] using commutes coreGeneratorB
  rcases commuting_matrix_cases ha hb with h | h | h | h
  · exact (Units.ne_zero g.val h).elim
  · exact Or.inl (Subtype.ext (Units.ext h))
  · exact Or.inr (Or.inr (Subtype.ext (Units.ext (h.trans coe_scalarUnit_sq.symm))))
  · exact Or.inr (Or.inl (Subtype.ext (Units.ext (h.trans coe_scalarUnit.symm))))

@[simp] theorem referenceProjection_scalar : referenceProjection referenceScalar = 1 := by
  apply (projection_eq_one_iff _).mpr
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  change scalarUnit * x.val * scalarUnit⁻¹ = x.val
  have h := congrArg Subtype.val (mem_center_iff.mp coreScalar_mem_center x)
  change x.val * scalarUnit = scalarUnit * x.val at h
  rw [← h, mul_assoc, mul_inv_cancel, mul_one]

theorem referenceProjection_kernel : referenceProjection.ker = referenceScalarGroup := by
  apply le_antisymm
  · intro g hg
    rcases conjugation_eq_one_cases g ((projection_eq_one_iff g).mp hg) with rfl | rfl | rfl
    · exact referenceScalarGroup.one_mem
    · exact mem_zpowers _
    · exact referenceScalarGroup.pow_mem (mem_zpowers _) 2
  · exact zpowers_le.mpr referenceProjection_scalar

theorem mem_referenceScalarGroup (g : Model) :
    g ∈ referenceScalarGroup ↔ g = 1 ∨ g = referenceScalar ∨ g = referenceScalar ^ 2 := by
  constructor
  · intro hg
    rw [← referenceProjection_kernel] at hg
    exact conjugation_eq_one_cases g ((projection_eq_one_iff g).mp hg)
  · rintro (rfl | rfl | rfl)
    · exact referenceScalarGroup.one_mem
    · exact mem_zpowers _
    · exact referenceScalarGroup.pow_mem (mem_zpowers _) 2

theorem referenceScalar_fixed_iff (v : Space) :
    action referenceScalar v = v ↔ v = 0 := M22TripleCover.scalar_fixed_iff v

private theorem scalar_sq_fixed_iff (v : Space) :
    action (referenceScalar ^ 2) v = v ↔ v = 0 := by
  constructor
  · intro hv
    apply (referenceScalar_fixed_iff v).mp
    have h := congrArg (action referenceScalar) hv
    rw [← Module.End.mul_apply, ← map_mul, ← pow_succ', referenceScalar_cube,
      map_one, Module.End.one_apply] at h
    exact h.symm
  · rintro rfl
    exact map_zero _

/-- The quotient is faithful on every nonzero *binary* vector stabilizer. -/
theorem referenceProjection_point_injective (v : Space) (hv : v ≠ 0) :
    Function.Injective (referenceProjection.comp (pointCentralizer v).subtype) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro g hg
  apply Subtype.ext
  have hk : g.val ∈ referenceScalarGroup := referenceProjection_kernel ▸ hg
  rcases (mem_referenceScalarGroup g.val).mp hk with h | h | h
  · exact h
  · exact (hv ((referenceScalar_fixed_iff v).mp (h ▸ g.property))).elim
  · exact (hv ((scalar_sq_fixed_iff v).mp (h ▸ g.property))).elim

/-- The three nonzero points of the associated F₄-line, in column coordinates. -/
def referenceScalarOrbit (v : Space) : Set Space :=
  {v, action referenceScalar v, action (referenceScalar ^ 2) v}

theorem mem_referenceScalarOrbit (v w : Space) :
    w ∈ referenceScalarOrbit v ↔ ∃ s ∈ referenceScalarGroup, action s v = w := by
  constructor
  · rintro (rfl | rfl | rfl)
    · exact ⟨1, referenceScalarGroup.one_mem, by simp⟩
    · exact ⟨referenceScalar, mem_zpowers _, rfl⟩
    · exact ⟨referenceScalar ^ 2, referenceScalarGroup.pow_mem (mem_zpowers _) 2, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    rcases (mem_referenceScalarGroup s).mp hs with rfl | rfl | rfl
    · exact Or.inl (by simp)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

/-- Scalar adjustment identifies the quotient image of the binary stabilizer.
This statement uses the literal three-element orbit, with no line-stabilizer
recognition assumed. -/
theorem projection_mem_point_image_iff (v : Space) (g : Model) :
    referenceProjection g ∈ (pointCentralizer v).map referenceProjection ↔
      action g v ∈ referenceScalarOrbit v := by
  rw [mem_referenceScalarOrbit]
  constructor
  · rintro ⟨h, hh, hq⟩
    refine ⟨g * h⁻¹, ?_, ?_⟩
    · rw [← referenceProjection_kernel, MonoidHom.mem_ker, map_mul, map_inv, hq,
        mul_inv_cancel]
    · have hh' : action h⁻¹ v = v := (pointCentralizer v).inv_mem hh
      rw [map_mul, Module.End.mul_apply, hh']
  · rintro ⟨s, hs, hsg⟩
    have hsq : referenceProjection s = 1 := by
      change s ∈ referenceProjection.ker
      rwa [referenceProjection_kernel]
    refine mem_map.mpr ⟨s⁻¹ * g, ?_, ?_⟩
    · change action (s⁻¹ * g) v = v
      rw [map_mul, Module.End.mul_apply, ← hsg, ← Module.End.mul_apply,
        ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    · rw [map_mul, map_inv, hsq, inv_one, one_mul]

/-- The quotient restriction gives an honest equivalence with its actual image. -/
def pointCentralizerEquivProjectionImage (v : Space) (hv : v ≠ 0) :
    pointCentralizer v ≃* (pointCentralizer v).map referenceProjection :=
  MulEquiv.ofBijective (referenceProjection.subgroupMap (pointCentralizer v))
    ⟨fun _ _ h => referenceProjection_point_injective v hv
      (congrArg (fun z : (pointCentralizer v).map referenceProjection => z.val) h),
      referenceProjection.subgroupMap_surjective _⟩

@[simp] theorem pointCentralizerEquivProjectionImage_apply (v : Space) (hv : v ≠ 0)
    (x : pointCentralizer v) :
    (pointCentralizerEquivProjectionImage v hv x).val = referenceProjection x.val := rfl

/-- Native unordered-pair stabilizer in the degree-22 design group. -/
def referencePairStabilizer (p : Finset (Fin 22)) : Subgroup m22DesignAut :=
  MulAction.stabilizer m22DesignAut p

/-- A projective geometric comparison identifies the actual binary image. -/
theorem point_image_eq_pair (v : Space) (p : Finset (Fin 22))
    (hgeom : ∀ g : Model, action g v ∈ referenceScalarOrbit v ↔
      referenceProjection g ∈ referencePairStabilizer p) :
    (pointCentralizer v).map referenceProjection = referencePairStabilizer p := by
  ext x
  obtain ⟨g, rfl⟩ := referenceProjection_surjective x
  exact (projection_mem_point_image_iff v g).trans (hgeom g)

/-- Apply the scalar adjustment and injectivity to the actual reference vector. -/
def referencePointCentralizerEquivPair (p : Finset (Fin 22))
    (hgeom : ∀ g : Model, action g referenceVector ∈ referenceScalarOrbit referenceVector ↔
      referenceProjection g ∈ referencePairStabilizer p) :
    pointCentralizer referenceVector ≃* referencePairStabilizer p :=
  (pointCentralizerEquivProjectionImage referenceVector referenceVector_ne_zero).trans
    (MulEquiv.subgroupCongr (point_image_eq_pair referenceVector p hgeom))

@[simp] theorem referencePointCentralizerEquivPair_apply (p : Finset (Fin 22))
    (hgeom : ∀ g : Model, action g referenceVector ∈ referenceScalarOrbit referenceVector ↔
      referenceProjection g ∈ referencePairStabilizer p)
    (x : pointCentralizer referenceVector) :
    (referencePointCentralizerEquivPair p hgeom x).val = referenceProjection x.val := rfl

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.Native
