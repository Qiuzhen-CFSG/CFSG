module

public import Theory.SpecificGroups.PSL3Four.CentralCover.ElementaryParabolic.Lifting
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.ParabolicResiduals
public import Theory.SpecificGroups.PSL3.LinearThreeOuterExtensions.Locals
public import Theory.SpecificGroups.PSL3.RootPlaneGeometry
public import Theory.GroupTheory.PCoreFrattiniTransport

/-!
# The actual residuals of parabolic preimages

Restriction of the covering map sends each lifted parabolic's solvable residual
onto its projective root local. Its affine coordinates identify the quotient
by the two-core with SL₂(4). Elementary-kernel involution lifting shows that the
original residual two-core is elementary, rather than merely its image.

Source: Aschbacher--Smith I.2.2(3b) and its use in 2.5.7, pp.554--555.
-/

@[expose] public section
noncomputable section
open Subgroup
open scoped MatrixGroups
namespace Matrix.PSL3Four.ElementaryParabolic
open Matrix.PSL3.LinearThree Matrix.PSL3.LinearThree.OuterExtensions
open Matrix.PSL3.RootPlaneGeometry
variable {E : Type*} [Group E] [Finite E]

abbrev liftedParabolic (f : E →* PSL) (b : Bool) : Subgroup E :=
  (parabolic F b).comap f

abbrev liftedResidual (f : E →* PSL) (b : Bool) := solvableResidual (liftedParabolic f b)

/-- The source residual maps onto the literal root local. -/
theorem residual_image (f : E →* PSL) (hf : Function.Surjective f) (b : Bool) :
    ((liftedResidual f b).map (liftedParabolic f b).subtype).map f = localFactor F b := by
  rw [map_solvableResidual_comap f hf]
  cases b
  · exact ParabolicResiduals.lineParabolic_residual F (by simp [card_F])
  · exact ParabolicResiduals.pointParabolic_residual F (by simp [card_F])

/-- The actual restriction, not an unmarked model equivalence. -/
def residualMap (f : E →* PSL) (hf : Function.Surjective f) (b : Bool) :
    liftedResidual f b →* localFactor F b :=
  ((f.comp (liftedParabolic f b).subtype).comp (liftedResidual f b).subtype).codRestrict _ (by
    intro x
    rw [← residual_image f hf b]
    exact mem_map_of_mem f (mem_map_of_mem _ x.property))

theorem residualMap_surjective (f : E →* PSL) (hf : Function.Surjective f) (b : Bool) :
    Function.Surjective (residualMap f hf b) := by
  intro y
  obtain ⟨_, ⟨x, hx, rfl⟩, he⟩ := (residual_image f hf b).ge y.property
  exact ⟨⟨x, hx⟩, Subtype.ext he⟩

/-- Point coordinates use duality, consistently with the existing local maps. -/
noncomputable def localAffine (b : Bool) : localFactor F b ≃* Matrix.SL2.Affine F := by
  cases b
  · exact lineLocalEquivAffine F
  · exact pointLocalEquivAffine F

noncomputable def residualAffine (f : E →* PSL) (hf : Function.Surjective f) (b : Bool) :
    liftedResidual f b →* Matrix.SL2.Affine F :=
  (localAffine b).toMonoidHom.comp (residualMap f hf b)

theorem residualAffine_surjective (f : E →* PSL) (hf : Function.Surjective f) (b : Bool) :
    Function.Surjective (residualAffine f hf b) :=
  (localAffine b).surjective.comp (residualMap_surjective f hf b)

@[simp] theorem residualAffine_ker (f : E →* PSL) (hf : Function.Surjective f) (b : Bool) :
    (residualAffine f hf b).ker =
      (f.ker.comap (liftedParabolic f b).subtype).comap (liftedResidual f b).subtype := by
  ext x
  change localAffine b (residualMap f hf b x) = 1 ↔ f x.val.val = 1
  rw [← (localAffine b).map_one, (localAffine b).injective.eq_iff]
  exact Subtype.ext_iff

theorem residualAffine_ker_isTwoGroup
    (f : E →* PSL) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) (b : Bool) :
    IsPGroup 2 (residualAffine f hf b).ker := by
  rw [residualAffine_ker]
  exact (hk.comap_of_injective _ (liftedParabolic f b).subtype_injective).comap_of_injective
    _ (liftedResidual f b).subtype_injective

/-- The intrinsic two-core is exactly the inverse image of translations. -/
theorem residualCore_eq (f : E →* PSL) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (b : Bool) : pCore 2 (liftedResidual f b) =
      (Matrix.SL2.translations F).comap (residualAffine f hf b) := by
  rw [← Matrix.SL2.affine_twoCore_eq]
  exact ((residualAffine f hf b).comap_pCore_of_ker_isPGroup
    (residualAffine_surjective f hf b) (residualAffine_ker_isTwoGroup f hf hk b)).symm

/-- No nontrivial Frattini layer remains in the original residual core. -/
theorem residualCore_elementary (f : E →* PSL) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (hs : ∀ z ∈ f.ker, z ^ 2 = 1) (b : Bool) :
    IsElementaryAbelian 2 (pCore 2 (liftedResidual f b)) := by
  have hk : IsPGroup 2 f.ker := fun z => ⟨1, by simpa using Subtype.ext (hs z z.property)⟩
  have hpow (x : pCore 2 (liftedResidual f b)) : x ^ 2 = 1 := by
    have hx : residualAffine f hf b x.val ∈ Matrix.SL2.translations F := by
      exact (residualCore_eq f hf hk b).le x.property
    have ha := elemPow_eq_one_of_isElementaryAbelian (p := 2) (residualAffine f hf b x.val) hx
    change (localAffine b (residualMap f hf b x.val)) ^ 2 = 1 at ha
    have hl : (residualMap f hf b x.val) ^ 2 = 1 :=
      (localAffine b).injective (by simpa only [map_pow, map_one] using ha)
    have hp : (f x.val.val.val) ^ 2 = 1 := congrArg Subtype.val hl
    have hx2 := ExtendedCentralizer.CoverCentralizers.CentralTwist.square_eq_one_of_elementary_kernel
      f hf hc hs x.val.val.val hp
    exact Subtype.ext (Subtype.ext (Subtype.ext hx2))
  exact {
    toIsMulCommutative := ⟨⟨fun x y => Commute.of_orderOf_dvd_two
      (fun z => orderOf_dvd_of_pow_eq_one (hpow z)) x y⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpow }

theorem residualCore_frattini (f : E →* PSL) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (hs : ∀ z ∈ f.ker, z ^ 2 = 1) (b : Bool) :
    frattini (pCore 2 (liftedResidual f b)) = ⊥ := by
  let := residualCore_elementary f hf hc hs b
  let : Fact (IsPGroup 2 (pCore 2 (liftedResidual f b))) := ⟨pCore_isPGroup⟩
  exact frattini_eq_bot_of_isElementaryAbelian (p := 2)

/-- The quotient of the actual source residual by its two-core. -/
noncomputable def residualCoreQuotientEquiv
    (f : E →* PSL) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) (b : Bool) :
    (liftedResidual f b ⧸ pCore 2 (liftedResidual f b)) ≃* SL(2,F) :=
  ((residualAffine f hf b).pCoreQuotientEquiv (residualAffine_surjective f hf b)
    (residualAffine_ker_isTwoGroup f hf hk b)).trans (Matrix.SL2.affineCoreQuotientEquiv F)

@[simp] theorem residualCoreQuotientEquiv_mk
    (f : E →* PSL) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) (b : Bool)
    (x : liftedResidual f b) :
    residualCoreQuotientEquiv f hf hk b (QuotientGroup.mk' _ x) =
      (residualAffine f hf b x).right := rfl

end Matrix.PSL3Four.ElementaryParabolic

end
