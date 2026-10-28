module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.Cardinalities
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Transport
public import Theory.Representation.CentralCoverOriginalAction.Quadratic
public import Theory.Representation.SL3OddNaturalNormalizer.Semilinear
public import Theory.Representation.SymplecticConjugatePair.Ambient.Normalizer.Commutant

/-!
# Semilinearity on the original remaining natural module

For both full SL₃ and Sp₄ markings, the additive commutant consists of field
scalars. An element normalizing V also normalizes L by the source normalizer
control, and hence permutes these scalars. Its action on the original quotient
is therefore semilinear. The actual Sylow action is a restriction of this
action. No projective quotient, assumed field-linearity, or exclusion of q=4
is used.

The quotient-action argument adapts the SL₃ calculation in the retained
Amalgam/Even/Linear/Action proof to both remaining models.
Source: Aschbacher--Smith, 11.4.4--11.5.3, printed pp.778--780.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.LineAlignment
open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry

private theorem semilinear_of_natural_quotient
    {F H K N : Type*} [Field F] [Finite F] [Group H] [Group K]
    [AddCommGroup N] [Module F N] [Module (ZMod 2) N] [Nontrivial N]
    (J : Subgroup H) [J.Normal] (q : J →* K) (hq : Function.Surjective q)
    (τ : Representation F K N)
    (hc : OneCohomology.CentralCoverOriginalAction.HasScalarCommutant τ)
    (ρ : Representation (ZMod 2) H N)
    (hnat : ∀ (j : J) v, ρ (j : H) v = τ (q j) v)
    (h : H) : ∃ σ : F ≃+* F, ∀ c v, ρ h (c • v) = σ c • ρ h v := by
  let a := J.normalizerMonoidHom ⟨h, J.normalizer_eq_top ▸ mem_top h⟩
  let e := LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom h)
  have hc' : OneCohomology.CentralCoverOriginalAction.HasScalarCommutant (τ.comp q) := by
    intro f hf
    apply hc f
    intro j v
    obtain ⟨k, rfl⟩ := hq j
    exact hf k v
  apply OneCohomology.CentralCoverOriginalAction.normalizer_semilinear (τ.comp q) hc' a e
  intro j v
  change ρ h (τ (q j) v) = τ (q (a j)) (ρ h v)
  rw [← hnat, ← hnat]
  change ρ h (ρ (j : H) v) = ρ (h * (j : H) * h⁻¹) (ρ h v)
  simp only [← Module.End.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel, mul_one]

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {E : Geometry D} (F₀ : MarkedFlag E)

/-- Both remaining full natural actions have the additive scalar commutant. -/
theorem model_scalar_commutant :
    OneCohomology.CentralCoverOriginalAction.HasScalarCommutant
      F₀.action.coordinates.modelAction := by
  cases F₀.action with
  | sl3 m =>
    intro f hf
    exact SL3OddNaturalNormalizer.centralizer_scalar f hf
  | sp4 m =>
    intro f hf
    exact SymplecticConjugatePair.Ambient.Normalizer.Commutant.natural_centralizer_scalar
      f (fun g v => hf g.val v)

/-- Source normalizer control gives semilinearity of the actual quotient action. -/
theorem normalizer_semilinear
    (hNV : normalizer (V : Set G) ≤ normalizer (L : Set G)) (a : normalizer (V : Set G)) :
    ∃ σ : E.input.field.Carrier ≃+* E.input.field.Carrier, ∀ t v,
      F₀.action.coordinates.conjugationAction hNV le_rfl a (t • v) =
        σ t • F₀.action.coordinates.conjugationAction hNV le_rfl a v := by
  let c := F₀.action.coordinates
  let H := normalizer (V : Set G)
  let J := L.subgroupOf H
  let e : J ≃* L := subgroupOfEquivOfLe D.normalizes
  let q : J →* c.ModelGroup := c.quotientMap.comp e.toMonoidHom
  let _ : J.Normal := normal_subgroupOf_of_le_normalizer hNV
  have : Nontrivial c.Space := by
    cases ha : F₀.action <;> simp only [c, ha, RemainingAction.coordinates, Coordinates.Space] <;>
      infer_instance
  apply semilinear_of_natural_quotient J q
    (c.quotientMap_surjective.comp e.surjective) c.modelAction (model_scalar_commutant F₀)
    (c.conjugationAction hNV le_rfl)
  intro j x
  obtain ⟨v, hv⟩ := c.projection_surjective (Multiplicative.ofAdd x)
  have he : (c.projection v).toAdd = x := congrArg Multiplicative.toAdd hv
  rw [← he]
  change c.conjugationAction hNV le_rfl (j : H) (c.projection v).toAdd =
    c.modelAction (c.quotientMap (e j)) (c.projection v).toAdd
  rw [c.conjugationAction_projection, ← c.projection_component_conjugation]
  rfl

/-- Each actor in the original Sylow subgroup is semilinear on the same model. -/
theorem sylow_semilinear
    (hNV : normalizer (V : Set G) ≤ normalizer (L : Set G)) (a : T) :
    ∃ σ : E.input.field.Carrier ≃+* E.input.field.Carrier, ∀ t v,
      F₀.action.coordinates.conjugationAction D.sylow_normalizes_component
          E.input.sylow_normalizes a (t • v) =
        σ t • F₀.action.coordinates.conjugationAction D.sylow_normalizes_component
          E.input.sylow_normalizes a v := by
  let c := F₀.action.coordinates
  have he (x : c.Space) : c.conjugationAction hNV le_rfl
      (inclusion E.input.sylow_normalizes a) x =
      c.conjugationAction D.sylow_normalizes_component E.input.sylow_normalizes a x := by
    obtain ⟨v, hv⟩ := c.projection_surjective (Multiplicative.ofAdd x)
    rw [← show (c.projection v).toAdd = x from congrArg Multiplicative.toAdd hv,
      c.conjugationAction_projection, c.conjugationAction_projection]
    rfl
  obtain ⟨σ, hσ⟩ := normalizer_semilinear F₀ hNV (inclusion E.input.sylow_normalizes a)
  exact ⟨σ, fun t v => (he _).symm.trans ((hσ t v).trans (congrArg (σ t • ·) (he _)))⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.LineAlignment
