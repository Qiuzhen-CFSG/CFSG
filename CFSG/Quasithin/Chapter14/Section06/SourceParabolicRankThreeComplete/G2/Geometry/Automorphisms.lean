module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.G2.Intrinsic
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction
import all CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction
public import Theory.Representation.G2BinaryNaturalNormalizer
public import Theory.Representation.CentralCoverOriginalAction

/-!
# Whole-module coordinates for automorphisms of a G₂ block

The induced natural-module automorphism normalizes the derived G₂ action,
so it is an actual full G₂(2) operator. In the Weyl alternative, uniqueness
of lifts from a commutator-generated cover identifies the action on the whole
seven-space over the original six-dimensional projection. The fixed central
kernel is retained throughout.

The private import is an intentional proof extension of AutomorphismAction,
needed to compare its actor with the literal quotient map. No private name
occurs in the exported statements, and the shared module is unchanged.

Source: Aschbacher--Smith, original 14.6.10(5), printed p.1029, using
C.1.30 and I.1.5--6. Concrete G₂ models: LICENSES/ATLAS.txt.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.G2SecondParabolic
open ChapterC ChapterC.ExceptionalRestrictions Atlas.G2.Natural
variable {K : Type*} [Group K]

/-- The additive natural-module operator induced by an actual block automorphism. -/
def naturalAut (m : BlockModuleModel K g2TwoNaturalAction) (a : MulAut K) :
    Space (ZMod 2) ≃ₗ[ZMod 2] Space (ZMod 2) :=
  { (AddEquiv.toMultiplicative.symm (m.moduleAction a)) with
    map_smul' := ZMod.map_smul (AddEquiv.toMultiplicative.symm (m.moduleAction a)) }

theorem naturalAut_compatible (m : BlockModuleModel K g2TwoNaturalAction) (a : MulAut K)
    (g : commutator (Atlas.G2.Model (ZMod 2))) (v : Space (ZMod 2)) :
    naturalAut m a (derivedAction (ZMod 2) g v) =
      derivedAction (ZMod 2) (m.quotientAction a g) (naturalAut m a v) :=
  congrArg Multiplicative.toAdd (m.actions_compatible a g (Multiplicative.ofAdd v))

/-- Normalizing the derived action gives an actual full G₂ actor. -/
theorem naturalAut_actor (m : BlockModuleModel K g2TwoNaturalAction) (a : MulAut K) :
    ∃ g : Atlas.G2.Model (ZMod 2), ∀ v, naturalAut m a v = action (ZMod 2) g v := by
  let t := LinearMap.GeneralLinearGroup.ofLinearEquiv (naturalAut m a)
  have he (x : commutator (Atlas.G2.Model (ZMod 2))) :
      t * (derivedAction (ZMod 2)).asGroupHom x * t⁻¹ =
        (derivedAction (ZMod 2)).asGroupHom (m.quotientAction a x) := by
    apply Units.ext
    apply LinearMap.ext
    intro v
    change naturalAut m a (derivedAction (ZMod 2) x ((naturalAut m a).symm v)) = _
    rw [naturalAut_compatible, LinearEquiv.apply_symm_apply]
    rfl
  have ht : t ∈ linearNormalizer (derivedAction (ZMod 2)) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply le_antisymm
    · rintro _ ⟨_, ⟨x,rfl⟩, rfl⟩
      exact ⟨m.quotientAction a x, (he x).symm⟩
    · rintro _ ⟨x,rfl⟩
      refine ⟨(derivedAction (ZMod 2)).asGroupHom ((m.quotientAction a).symm x),
        ⟨_,rfl⟩, ?_⟩
      change t * _ * t⁻¹ = _
      rw [he, MulEquiv.apply_symm_apply]
  exact BinaryNormalizer.exists_natural_actor ⟨t,ht⟩

variable [IsElementaryAbelian 2 (blockU K)]

/-- Automorphisms of K act on the whole characteristic U-layer. -/
def intrinsicAut (a : MulAut K) : Additive (blockU K) ≃ₗ[ZMod 2] Additive (blockU K) :=
  { (MulAut.characteristic (blockU K) a).toAdditive with
    map_smul' := ZMod.map_smul (MulAut.characteristic (blockU K) a).toAdditive }

theorem intrinsicAut_projection (m : BlockModuleModel K g2TwoNaturalAction)
    (a : MulAut K) (v : Additive (blockU K)) :
    intrinsicProjection m (intrinsicAut a v) = naturalAut m a (intrinsicProjection m v) :=
  (congrArg Multiplicative.toAdd (m.moduleAction_mk a v.toMul)).symm

theorem intrinsicAut_equivariant (h : IsShort K) (m : BlockModuleModel K g2TwoNaturalAction)
    (a : MulAut K) (x : commutator (Atlas.G2.Model (ZMod 2)))
    (v : Additive (blockU K)) :
    intrinsicAut a (intrinsicAction h m x v) =
      intrinsicAction h m (m.quotientAction a x) (intrinsicAut a v) := by
  obtain ⟨k,rfl⟩ := m.actor_surjective x
  rw [m.quotientAction_actor]
  change intrinsicAut a (intrinsicAction h m (m.quotientIso (QuotientGroup.mk' _ k)) v) =
    intrinsicAction h m (m.quotientIso (QuotientGroup.mk' _ (a k))) (intrinsicAut a v)
  rw [intrinsicAction_apply, intrinsicAction_apply]
  apply Additive.toMul.injective
  apply Subtype.ext
  change a (k * (v.toMul : K) * k⁻¹) = a k * a (v.toMul : K) * (a k)⁻¹
  simp only [map_mul,map_inv]

/-- The same coordinates extend from the derived actor to every automorphism
in the six-dimensional alternative. -/
theorem natural_coordinates_automorphism (m : BlockModuleModel K g2TwoNaturalAction)
    (E : Additive (blockU K) ≃ₗ[ZMod 2] Space (ZMod 2))
    (hE : ∀ v, E v = intrinsicProjection m v) (a : MulAut K) :
    ∃ g : Atlas.G2.Model (ZMod 2), ∀ v,
      E (intrinsicAut a v) = action (ZMod 2) g (E v) := by
  obtain ⟨g,hg⟩ := naturalAut_actor m a
  exact ⟨g, fun v => by rw [hE, intrinsicAut_projection, hg, ← hE]⟩

omit [IsElementaryAbelian 2 (blockU K)] in
/-- The full actor induces the same automorphism of the derived group. -/
theorem naturalAut_actor_conjugates (m : BlockModuleModel K g2TwoNaturalAction)
    (a : MulAut K) (g : Atlas.G2.Model (ZMod 2))
    (hg : ∀ v, naturalAut m a v = action (ZMod 2) g v)
    (x : commutator (Atlas.G2.Model (ZMod 2))) :
    (m.quotientAction a x : Atlas.G2.Model (ZMod 2)) = g * x * g⁻¹ := by
  apply action_injective (ZMod 2)
  apply LinearMap.ext
  intro v
  have he := naturalAut_compatible m a x (action (ZMod 2) g⁻¹ v)
  rw [hg, hg] at he
  have hi : action (ZMod 2) g (action (ZMod 2) g⁻¹ v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  rw [hi] at he
  exact he.symm.trans (by
    change action (ZMod 2) g (action (ZMod 2) x.val (action (ZMod 2) g⁻¹ v)) = _
    simp only [map_mul, Module.End.mul_apply])

/-- Uniqueness over the original central projection transports every block
normalizer to the same actual Weyl operator. -/
theorem weyl_coordinates_automorphism (h : IsShort K)
    (m : BlockModuleModel K g2TwoNaturalAction)
    (E : TraceZero (ZMod 2) ≃ₗ[ZMod 2] Additive (blockU K))
    (hE : ∀ x w, E (OrthogonalCover.binaryAction (ZMod 2) x w) =
      intrinsicAction h m x (E w))
    (hproj : ∀ w, intrinsicProjection m (E w) = mk (ZMod 2) w)
    (a : MulAut K) :
    ∃ g : Atlas.G2.Model (ZMod 2), ∀ w,
      intrinsicAut a (E w) = E (traceZeroAction (ZMod 2) g w) := by
  obtain ⟨g,hg⟩ := naturalAut_actor m a
  have hconj := naturalAut_actor_conjugates m a g hg
  let τ := (intrinsicAction h m).comp (m.quotientAction a).toMonoidHom
  have ht (x : commutator (Atlas.G2.Model (ZMod 2))) (w : TraceZero (ZMod 2)) :
      traceZeroAction (ZMod 2) g (OrthogonalCover.binaryAction (ZMod 2) x w) =
        OrthogonalCover.binaryAction (ZMod 2) (m.quotientAction a x)
          (traceZeroAction (ZMod 2) g w) := by
    change traceZeroAction (ZMod 2) g (traceZeroAction (ZMod 2) x.val w) =
      traceZeroAction (ZMod 2) (m.quotientAction a x).val (traceZeroAction (ZMod 2) g w)
    rw [hconj]
    simp only [← Module.End.mul_apply, ← map_mul]
    congr 2
    group
  have he := Representation.OneCohomology.CentralCoverOriginalAction.lift_unique
    (OrthogonalCover.binaryAction (ZMod 2)) τ
    (OrthogonalCover.binaryProjection_isCover (ZMod 2)).2.2
    (intrinsicProjection m)
    (fun v hv x => (intrinsicCover_isCover h m).2.1 hv (m.quotientAction a x))
    ((intrinsicAut a).toLinearMap.comp E.toLinearMap)
    (E.toLinearMap.comp (traceZeroAction (ZMod 2) g))
    (fun x w => by
      change intrinsicAut a (E (OrthogonalCover.binaryAction (ZMod 2) x w)) = _
      rw [hE, intrinsicAut_equivariant]
      rfl)
    (fun x w => by
      change E (traceZeroAction (ZMod 2) g (OrthogonalCover.binaryAction (ZMod 2) x w)) = _
      rw [ht,hE]
      rfl)
    (fun w => by
      change intrinsicProjection m (intrinsicAut a (E w)) =
        intrinsicProjection m (E (traceZeroAction (ZMod 2) g w))
      rw [intrinsicAut_projection, hproj, hproj, hg]
      rfl)
  exact ⟨g, fun w => LinearMap.congr_fun he w⟩

end CFSG.Quasithin.Chapter14.Section06.G2SecondParabolic
