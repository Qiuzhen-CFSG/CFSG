module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Transport
public import Theory.Representation.CentralCoverOriginalAction.Quadratic
public import Theory.Representation.SL3OddNaturalNormalizer.Semilinear
public import Theory.Representation.SymplecticConjugatePair.Ambient.Normalizer.Commutant

/-!
# Semilinearity of the original Sylow action in the Cartan coordinates

The supplied natural action has scalar additive commutant. Surjectivity
of the original L-to-model projection transfers that commutant to L.
Conjugation by the same element of T intertwines the original actions,
so it permutes the field scalars and is semilinear. This is proved for
both full SL3 and Sp4 markings before outside-component recognition.

Conjugating the operators by any chosen model element preserves that
same coefficient automorphism and the actual conjugation identity.
Thus CartanAlignment's simultaneous inner change of basis can be used
without changing the Sylow element or introducing an unrelated action.
The subsequent flag and Cartan-power calculation remains with this
parameter-component owner; final source assembly remains with
qt-d-1222-shadow-linear-geometry.

The scalar-commutant argument follows the generic natural-quotient proof
also used in Closure/Nonabelian/LineAlignment/Action, without importing
its downstream hypotheses or marking.
Source: Aschbacher--Smith, 11.3.5(2), printed pp.771--772.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Representation
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Paired
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}

/-- The original Sylow action intertwines the original component quotient
with conjugation by the same ambient element. -/
theorem sylowAction_intertwines (c : Coordinates D S.field) (t : T) (l : L)
    (v : c.Space) :
    c.sylowAction S t (c.modelAction (c.quotientMap l) v) =
      c.modelAction (c.quotientMap
        (L.normalizerMonoidHom (inclusion D.sylow_normalizes_component t) l))
          (c.sylowAction S t v) := by
  obtain ⟨w,hw⟩ := c.projection_surjective (Multiplicative.ofAdd v)
  have hv : (c.projection w).toAdd = v := congrArg Multiplicative.toAdd hw
  rw [←hv]
  change c.conjugationAction D.sylow_normalizes_component S.sylow_normalizes t _ = _
  rw [←c.projection_component_conjugation, c.conjugationAction_projection]
  change _ = c.modelAction _
    (c.conjugationAction D.sylow_normalizes_component S.sylow_normalizes t _)
  rw [c.conjugationAction_projection, ←c.projection_component_conjugation]
  congr 2
  apply Subtype.ext
  change (t : G) * ((l : G) * (w : G) * (l : G)⁻¹) * (t : G)⁻¹ =
    ((t : G)*(l : G)*(t : G)⁻¹) * ((t : G)*(w : G)*(t : G)⁻¹) *
      ((t : G)*(l : G)*(t : G)⁻¹)⁻¹
  group

/-- A scalar commutant makes the actual Sylow action semilinear, without
any outside-component natural marking or normalizer-control hypothesis. -/
theorem sylow_semilinear_of_scalar_commutant (c : Coordinates D S.field)
    [Nontrivial c.Space]
    (hc : OneCohomology.CentralCoverOriginalAction.HasScalarCommutant c.modelAction)
    (t : T) :
    ∃ σ : S.field.Carrier ≃+* S.field.Carrier, ∀ a v,
      c.sylowAction S t (a • v) = σ a • c.sylowAction S t v := by
  let a := L.normalizerMonoidHom (inclusion D.sylow_normalizes_component t)
  let e := LinearMap.GeneralLinearGroup.toLinearEquiv ((c.sylowAction S).asGroupHom t)
  have hc' : OneCohomology.CentralCoverOriginalAction.HasScalarCommutant
      (c.modelAction.comp c.quotientMap) := by
    intro f hf
    apply hc f
    intro g v
    obtain ⟨l,rfl⟩ := c.quotientMap_surjective g
    exact hf l v
  exact OneCohomology.CentralCoverOriginalAction.normalizer_semilinear
    (c.modelAction.comp c.quotientMap) hc' a e (sylowAction_intertwines c t)

/-- Semilinearity for the original full SL3 natural-action marking. -/
theorem source_sylow_semilinear_sl3
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) (t : T) :
    ∃ σ : S.field.Carrier ≃+* S.field.Carrier, ∀ (a : S.field.Carrier) (v : (Coordinates.sl3 m).Space),
      (Coordinates.sl3 m).sylowAction S t (a • v) =
        σ a • (Coordinates.sl3 m).sylowAction S t v := by
  let c : Coordinates D S.field := .sl3 m
  let : Nontrivial c.Space := inferInstanceAs (Nontrivial (Fin 3 → S.field.Carrier))
  apply sylow_semilinear_of_scalar_commutant c
  intro f hf
  exact SL3OddNaturalNormalizer.centralizer_scalar f hf

/-- Semilinearity for the original full Sp4 marking, including the field
of order four and the full group, with no derived-quotient replacement. -/
theorem source_sylow_semilinear_sp4
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2))) (t : T) :
    ∃ σ : S.field.Carrier ≃+* S.field.Carrier, ∀ (a : S.field.Carrier) (v : (Coordinates.sp4 m).Space),
      (Coordinates.sp4 m).sylowAction S t (a • v) =
        σ a • (Coordinates.sp4 m).sylowAction S t v := by
  let c : Coordinates D S.field := .sp4 m
  let : Nontrivial c.Space := inferInstanceAs (Nontrivial ((Fin 2 ⊕ Fin 2) → S.field.Carrier))
  apply sylow_semilinear_of_scalar_commutant c
  intro f hf
  exact SymplecticConjugatePair.Ambient.Normalizer.Commutant.natural_centralizer_scalar
    f (fun g v => hf g.val v)

/-- The original Sylow operator after the same inner coordinate change
used to align its inner Sylow and the actual Hall prime torsion. -/
def alignedSylowOperator (c : Coordinates D S.field) (b : c.ModelGroup) :
    T →* (c.Space ≃ₗ[ZMod 2] c.Space) :=
  (MulAut.conj (SymplecticConjugatePair.Ambient.linearAction
    (restrictScalars (k := ZMod 2) c.modelAction) b)).toMonoidHom.comp
      (SymplecticConjugatePair.Ambient.linearAction (c.sylowAction S))

theorem alignedSylowOperator_apply (c : Coordinates D S.field)
    (b : c.ModelGroup) (t : T) (v : c.Space) :
    alignedSylowOperator c b t v =
      c.modelAction b (c.sylowAction S t (c.modelAction b⁻¹ v)) := by
  change c.modelAction b (c.sylowAction S t
    ((SymplecticConjugatePair.Ambient.linearAction
      (restrictScalars (k := ZMod 2) c.modelAction) b)⁻¹ v)) = _
  rw [←map_inv]
  rfl

/-- The inner change of coordinates retains the coefficient automorphism
of the same original Sylow element. -/
theorem alignedSylowOperator_smul (c : Coordinates D S.field)
    (b : c.ModelGroup) (t : T) (σ : S.field.Carrier ≃+* S.field.Carrier)
    (hσ : ∀ a v, c.sylowAction S t (a • v) = σ a • c.sylowAction S t v)
    (a : S.field.Carrier) (v : c.Space) :
    alignedSylowOperator c b t (a • v) = σ a • alignedSylowOperator c b t v := by
  simp only [alignedSylowOperator_apply,map_smul,hσ]

/-- The aligned operator intertwines the same conjugation on L with its
original full group marking, conjugated by the same inner coordinate change. -/
theorem alignedSylowOperator_intertwines (c : Coordinates D S.field)
    (b : c.ModelGroup) (t : T) (l : L) (v : c.Space) :
    alignedSylowOperator c b t
      (c.modelAction (b*c.quotientMap l*b⁻¹) v) =
        c.modelAction (b*c.quotientMap
          (L.normalizerMonoidHom (inclusion D.sylow_normalizes_component t) l)*b⁻¹)
            (alignedSylowOperator c b t v) := by
  have hi (w : c.Space) : c.modelAction b⁻¹ (c.modelAction b w) = w := by
    rw [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply]
  simpa only [alignedSylowOperator_apply,map_mul,Module.End.mul_apply,hi] using
    congrArg (c.modelAction b) (sylowAction_intertwines c t l (c.modelAction b⁻¹ v))

/-- The common field action for any chosen inner alignment of the original SL3 marking. -/
theorem source_aligned_semilinear_sl3
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (b : (Coordinates.sl3 m).ModelGroup) (t : T) :
    ∃ σ : S.field.Carrier ≃+* S.field.Carrier, ∀ a v,
      alignedSylowOperator (Coordinates.sl3 m) b t (a • v) =
        σ a • alignedSylowOperator (Coordinates.sl3 m) b t v := by
  obtain ⟨σ,hσ⟩ := source_sylow_semilinear_sl3 m t
  exact ⟨σ,alignedSylowOperator_smul (Coordinates.sl3 m) b t σ hσ⟩

/-- The common field action for any chosen inner alignment of the original Sp4 marking. -/
theorem source_aligned_semilinear_sp4
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (b : (Coordinates.sp4 m).ModelGroup) (t : T) :
    ∃ σ : S.field.Carrier ≃+* S.field.Carrier, ∀ a v,
      alignedSylowOperator (Coordinates.sp4 m) b t (a • v) =
        σ a • alignedSylowOperator (Coordinates.sp4 m) b t v := by
  obtain ⟨σ,hσ⟩ := source_sylow_semilinear_sp4 m t
  exact ⟨σ,alignedSylowOperator_smul (Coordinates.sp4 m) b t σ hσ⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Paired
