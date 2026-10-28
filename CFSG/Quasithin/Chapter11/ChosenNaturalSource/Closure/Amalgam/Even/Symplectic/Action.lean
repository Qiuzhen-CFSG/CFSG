module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Transport
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even.Geometry
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Setup
public import Theory.Representation.CentralCoverOriginalAction.Quadratic
public import Theory.Representation.SymplecticConjugatePair.Ambient.Normalizer.Commutant

/-!
# Semilinearity on the actual chosen Sp₄ quotient

The additive commutant of the full natural Sp₄ action consists of scalars.
An ambient normalizer therefore permutes these scalars through a field
automorphism. Apply this to N_G(V), using source normalizer control and
the surjection L → L/O₂(L) ≃ Sp₄, retaining the full center.
Source: Aschbacher--Smith, 11.5.8, refs/quasithin.pdf, printed p.784.
-/

public noncomputable section
open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even.Symplectic

private theorem semilinear_of_natural_quotient
    {F H : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F] [CharP F 2] [Group H]
    (J : Subgroup H) [J.Normal]
    (q : J →* Matrix.symplecticGroup (Fin 2) F) (hq : Function.Surjective q)
    (ρ : Representation (ZMod 2) H (Fin 2 ⊕ Fin 2 → F))
    (hnat : ∀ (j : J) v, ρ (j : H) v = symplecticNatural 2 (q j) v)
    (h : H) : ∃ σ : F ≃+* F, ∀ c v, ρ h (c • v) = σ c • ρ h v := by
  let τ := (symplecticNatural (k := F) 2).comp q
  let a := J.normalizerMonoidHom ⟨h, J.normalizer_eq_top ▸ mem_top h⟩
  let e := LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom h)
  have hc : OneCohomology.CentralCoverOriginalAction.HasScalarCommutant τ := by
    intro f hf
    apply SymplecticConjugatePair.Ambient.Normalizer.Commutant.natural_centralizer_scalar f
    intro j v
    obtain ⟨k, hk⟩ := hq j.val
    rw [← hk]
    exact hf k v
  apply OneCohomology.CentralCoverOriginalAction.normalizer_semilinear τ hc a e
  intro j v
  change ρ h (symplecticNatural 2 (q j) v) =
    symplecticNatural 2 (q (a j)) (ρ h v)
  rw [← hnat, ← hnat]
  change ρ h (ρ (j : H) v) = ρ (h * (j : H) * h⁻¹) (ρ h v)
  simp only [← Module.End.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel, mul_one]

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} {E : Closure.Geometry D}
  (m : ActionEquiv D.centralQuotientAction (restrictScalars (k := ZMod 2) (symplecticNatural (k := E.input.field.Carrier) 2)))

/-- The actual full seed normalizer acts on the original marked quotient. -/
@[expose] def normalizerAction : Representation (ZMod 2) (normalizer (V : Set G))
    (Coordinates.sp4 m).Space :=
  (Coordinates.sp4 m).conjugationAction
    (WeakClosure.seed_normalizer_le D E.input) le_rfl

/-- Every element of the actual seed normalizer is semilinear, retaining the
full Sp₄ quotient and its center. -/
theorem normalizerAction_semilinear (a : normalizer (V : Set G)) :
    ∃ σ : E.input.field.Carrier ≃+* E.input.field.Carrier,
      ∀ c v, normalizerAction m a (c • v) = σ c • normalizerAction m a v := by
  let c := Coordinates.sp4 m
  let H := normalizer (V : Set G)
  let J := L.subgroupOf H
  let e : J ≃* L := subgroupOfEquivOfLe D.normalizes
  let q : J →* c.ModelGroup := c.quotientMap.comp e.toMonoidHom
  have hJ : J.Normal := normal_subgroupOf_of_le_normalizer
    (WeakClosure.seed_normalizer_le D E.input)
  let := hJ
  apply semilinear_of_natural_quotient J q
    (c.quotientMap_surjective.comp e.surjective) (normalizerAction m)
  intro j x
  obtain ⟨v, hv⟩ := c.projection_surjective (Multiplicative.ofAdd x)
  have he : (c.projection v).toAdd = x := congrArg Multiplicative.toAdd hv
  rw [← he]
  change c.conjugationAction (WeakClosure.seed_normalizer_le D E.input) le_rfl
    (j : H) (c.projection v).toAdd = c.modelAction (c.quotientMap (e j)) (c.projection v).toAdd
  rw [c.conjugationAction_projection, ← c.projection_component_conjugation]
  rfl

/-- Restricting the normalizer action gives exactly the descended action of
an ambient subgroup, on the same coordinates. -/
theorem normalizerAction_restrict (A : Subgroup G)
    (hAL : A ≤ normalizer (L : Set G)) (hAV : A ≤ normalizer (V : Set G))
    (a : A) (v : (Coordinates.sp4 m).Space) :
    normalizerAction m (inclusion hAV a) v =
      (Coordinates.sp4 m).conjugationAction hAL hAV a v := by
  let c := Coordinates.sp4 m
  obtain ⟨w, hw⟩ := c.projection_surjective (Multiplicative.ofAdd v)
  have he : (c.projection w).toAdd = v := congrArg Multiplicative.toAdd hw
  rw [← he]
  change c.conjugationAction _ _ _ _ = _
  rw [c.conjugationAction_projection, c.conjugationAction_projection]
  rfl

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even.Symplectic
