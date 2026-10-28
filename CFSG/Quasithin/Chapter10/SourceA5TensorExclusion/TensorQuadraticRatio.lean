module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorOuterWeakClosure.NonFF
public import Theory.Representation.OrthogonalFourPlusMatrix.QuadraticRatio
public import Theory.Representation.BinaryOffender.MarkedNormalizerRatio
public import Theory.Representation.BinaryOffender.DualDisplacement

/-!
# Numerical bounds for the original binary tensor action

The marked normal tensor subgroup puts every intermediate faithful actor
inside the full binary matrix normalizer. Its elementary rank estimates
therefore give quadratic ratio at least4/3. The invariant polar pairing
identifies the tensor subgroup with its dual, so the same normalizer
argument also excludes FF on the dual ambient action.

The final two theorems apply these facts to the literal full-module
normalizer in the source qrc configuration. They discharge the numerical
premises in the selection of a small-ratio chief factor in the PSL₃(4)
alternative; no irreducibility of a restricted chief module is asserted.

Source: Aschbacher--Smith9.2.7 and3.1.6, printed pp.731--732 and573--575;
the conjugate-generator bound is D.1.3(b), printed pp.173--174.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
variable {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)
include m

private theorem fullModule_image_marking
    (H : Subgroup G) (hLH : localOrbit T L ≤ H)
    (hHL : H ≤ normalizer (localOrbit T L : Set G))
    (hHV : H ≤ normalizer (D.fullModule : Set G)) :
    let := m.fullModule_elementary
    ∃ j : localOrbit T L →* ChapterD.internalActionImage H D.fullModule hHV,
      j.range.Normal ∧ Nonempty (Representation.Equiv
        ((ChapterD.UniqueFactor.imageRepresentation H D.fullModule hHV).comp j)
        (Binary.action.comp m.quotient)) := by
  classical
  let := m.fullModule_elementary
  let ρ := ChapterD.UniqueFactor.imageRepresentation H D.fullModule hHV
  let a := (ChapterD.UniqueFactor.actionHom H D.fullModule hHV).rangeRestrict
  let i : localOrbit T L →* H := inclusion hLH
  let j : localOrbit T L →* ChapterD.internalActionImage H D.fullModule hHV := a.comp i
  have hnormal : i.range.Normal := by
    have hi : i.range = (localOrbit T L).subgroupOf H := by
      ext x
      constructor
      · rintro ⟨y,rfl⟩
        exact y.property
      · intro hx
        exact ⟨⟨x,hx⟩,rfl⟩
    rw [hi]
    exact normal_subgroupOf_of_le_normalizer hHL
  let : i.range.Normal := hnormal
  have hjnormal : j.range.Normal := by
    rw [show j.range = i.range.map a from MonoidHom.range_comp _ _]
    exact Subgroup.Normal.map inferInstance a (MonoidHom.rangeRestrict_surjective _)
  let : j.range.Normal := hjnormal
  let c : D.fullModule ≃* Multiplicative Binary.V :=
    MulEquiv.ofBijective m.sectionData.coordinates ⟨m.coordinates_injective,m.sectionData.onto⟩
  let E : Additive D.fullModule ≃ₗ[ZMod 2] Binary.V :=
    { toFun := fun v => (c v.toMul).toAdd
      invFun := fun w => Additive.ofMul (c.symm (Multiplicative.ofAdd w))
      left_inv := fun _ => congrArg Additive.ofMul (c.symm_apply_apply _)
      right_inv := fun _ => congrArg Multiplicative.toAdd (c.apply_symm_apply _)
      map_add' := fun _ _ => congrArg Multiplicative.toAdd (c.map_mul _ _)
      map_smul' := ZMod.map_smul
        ({ toFun := fun v : Additive D.fullModule => (c v.toMul).toAdd
           map_zero' := congrArg Multiplicative.toAdd c.map_one
           map_add' := fun _ _ => congrArg Multiplicative.toAdd (c.map_mul _ _) } :
            Additive D.fullModule →+ Binary.V) }
  let b : Representation.Equiv (ρ.comp j) (Binary.action.comp m.quotient) :=
    { __ := E
      isIntertwining' h := by
        apply LinearMap.ext
        intro v
        exact m.sectionData.equivariant h v.toMul }
  exact ⟨j,hjnormal,⟨b⟩⟩

theorem fullModule_actionImage_quadraticRatio_four_thirds
    (H : Subgroup G) (hLH : localOrbit T L ≤ H)
    (hHL : H ≤ normalizer (localOrbit T L : Set G))
    (hHV : H ≤ normalizer (D.fullModule : Set G)) :
    let := m.fullModule_elementary
    (4 / 3 : ℝ≥0∞) ≤ quadraticRatio (ChapterD.UniqueFactor.imageRepresentation H D.fullModule hHV) := by
  let := m.fullModule_elementary
  obtain ⟨j,hn,⟨b⟩⟩ := m.fullModule_image_marking H hLH hHL hHV
  let := hn
  exact Binary.four_thirds_le_normalizer_quadraticRatio.trans
    (quadraticRatio_le_of_marked_normal_range _
      (ChapterD.UniqueFactor.imageRepresentation_injective H D.fullModule hHV)
      j Binary.action m.quotient m.onto b)

theorem fullModule_actionImage_dual_notFF
    (H : Subgroup G) (hLH : localOrbit T L ≤ H)
    (hHL : H ≤ normalizer (localOrbit T L : Set G))
    (hHV : H ≤ normalizer (D.fullModule : Set G)) :
    let := m.fullModule_elementary
    ¬ IsFFModule (ChapterD.UniqueFactor.imageRepresentation H D.fullModule hHV).dual := by
  let := m.fullModule_elementary
  let ρ := ChapterD.UniqueFactor.imageRepresentation H D.fullModule hHV
  obtain ⟨j,hn,⟨b⟩⟩ := m.fullModule_image_marking H hLH hHL hHV
  let := hn
  let bdual : Representation.Equiv (ρ.dual.comp j) (Binary.action.dual.comp m.quotient) :=
    .mk b.symm.toLinearEquiv.dualMap (fun g => by
      apply LinearMap.ext
      intro φ
      apply LinearMap.ext
      intro w
      change φ (ρ (j g)⁻¹ (b.symm w)) = φ (b.symm (Binary.action (m.quotient g)⁻¹ w))
      have he := Representation.IntertwiningMap.isIntertwining _ _ b.symm.toIntertwiningMap g⁻¹ w
      simpa only [ρ, MonoidHom.comp_apply, map_inv,
        Representation.Equiv.coe_toIntertwiningMap] using (congrArg φ he).symm)
  let c : Representation.Equiv (Binary.action.dual.comp m.quotient) (Binary.action.comp m.quotient) :=
    .mk Binary.actionSelfDual.symm.toLinearEquiv (fun g => by
      apply LinearMap.ext
      intro v
      exact Representation.IntertwiningMap.isIntertwining _ _
        Binary.actionSelfDual.symm.toIntertwiningMap (m.quotient g) v)
  exact Binary.not_ff_of_marked_normal_range ρ.dual
    (faithful_dual ρ (ChapterD.UniqueFactor.imageRepresentation_injective H D.fullModule hHV))
    j m.quotient m.onto (bdual.trans c)

/-- The actual full-module normalizer has the quantitative tensor bound. -/
theorem source_fullModule_quadraticRatio_four_thirds :
    letI := m.fullModule_elementary
    (4 / 3 : ℝ≥0∞) ≤ quadraticRatio
      (ChapterD.UniqueFactor.imageRepresentation (sourceFullModuleNormalizer D) D.fullModule
        (inf_le_left.trans D.maximalLocal_normalizes_fullModule)) :=
  m.fullModule_actionImage_quadraticRatio_four_thirds (sourceFullModuleNormalizer D)
    (le_sup_left.trans (source_localJoin_le_fullModuleNormalizer D)) inf_le_left
    (inf_le_left.trans D.maximalLocal_normalizes_fullModule)

/-- The dual-FF alternative of the original full-module numerical reduction is impossible. -/
theorem source_fullModule_dual_notFF : ¬ SourceFullModuleDualFF D :=
  m.fullModule_actionImage_dual_notFF (sourceFullModuleNormalizer D)
    (le_sup_left.trans (source_localJoin_le_fullModuleNormalizer D)) inf_le_left
    (inf_le_left.trans D.maximalLocal_normalizes_fullModule)

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
