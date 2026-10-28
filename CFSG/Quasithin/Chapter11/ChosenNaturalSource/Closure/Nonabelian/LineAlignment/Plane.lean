module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.LineAlignment.Displacement

/-!
# Line-bounded plane movement removes the field coefficient

The literal conjugate of V₁ is the preimage of its transported field line.
Each displacement on the marked plane is the projection of an actual ambient
commutator. Thus a single-line bound on [V₂,A] removes the field automorphism
from every A-element, by the two-dimensional displacement calculation. This
applies to elementary actors in particular, including at q=4.

The remaining transvection calculation must identify the nonzero commutator
with V₁; this module proves only field-linearity, not that identification.
Source: Aschbacher--Smith, 11.5.3(3), printed pp.779--780.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.LineAlignment
open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {E : Geometry D} (F₀ : MarkedFlag E)

theorem preimage_conjugate (c : Coordinates D E.input.field)
    (P : Submodule E.input.field.Carrier c.Space) (l : L) :
    (c.preimage P).map (MulAut.conj (l : G)).toMonoidHom =
      c.preimage (P.map (c.modelAction (c.quotientMap l))) := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    let v' : V := ⟨v, D.centralQuotientPreimage_le _ hv⟩
    apply (c.mem_preimage _ (V.normalizerMonoidHom (inclusion D.normalizes l) v')).mpr
    change (c.projection (V.normalizerMonoidHom (inclusion D.normalizes l) v')).toAdd ∈ _
    rw [c.projection_component_conjugation]
    exact ⟨(c.projection v').toAdd, (c.mem_preimage P v').mp hv, rfl⟩
  · intro v hv
    let v' : V := ⟨v, D.centralQuotientPreimage_le _ hv⟩
    let w := V.normalizerMonoidHom (inclusion D.normalizes l⁻¹) v'
    refine ⟨w, ?_, ?_⟩
    · apply (c.mem_preimage P w).mpr
      change (c.projection w).toAdd ∈ P
      dsimp only [w]
      rw [c.projection_component_conjugation]
      obtain ⟨x, hx, he⟩ := (c.mem_preimage _ v').mp hv
      change c.modelAction (c.quotientMap l) x = (c.projection v').toAdd at he
      rw [← he, map_inv, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      exact hx
    · change (l : G) * ((l : G)⁻¹ * v * ((l : G)⁻¹)⁻¹) * (l : G)⁻¹ = v
      group

theorem displacement_mem_line
    (A : Subgroup G) (hAT : A ≤ (T : Subgroup G)) (l : L)
    (hsmall : ⁅E.V₂, A⁆ ≤ E.V₁.map (MulAut.conj (l : G)).toMonoidHom)
    (a : A) (x : F₀.action.coordinates.Space) (hx : x ∈ F₀.flag.space 1) :
    F₀.action.coordinates.conjugationAction D.sylow_normalizes_component
      E.input.sylow_normalizes (inclusion hAT a) x - x ∈
        (F₀.flag.space 0).map
          (F₀.action.coordinates.modelAction (F₀.action.coordinates.quotientMap l)) := by
  let c := F₀.action.coordinates
  have hp : c.preimage (F₀.flag.space 1) = E.V₂ := by
    change D.centralQuotientPreimage _ = D.centralQuotientPreimage E.plane
    rw [F₀.plane_eq]
  have hq : c.preimage (F₀.flag.space 0) = E.V₁ := by
    change D.centralQuotientPreimage _ = D.centralQuotientPreimage E.point
    rw [F₀.point_eq]
  obtain ⟨v, hv⟩ := c.projection_surjective (Multiplicative.ofAdd x)
  have hvP : (v : G) ∈ E.V₂ := by
    rw [← hp]
    apply (c.mem_preimage _ v).mpr
    change (c.projection v).toAdd ∈ _
    rw [hv]
    exact hx
  let z := V.normalizerMonoidHom
    (inclusion E.input.sylow_normalizes (inclusion hAT a)) v * v⁻¹
  have hz : (z : G) ∈ E.V₁.map (MulAut.conj (l : G)).toMonoidHom := by
    apply hsmall
    rw [commutator_comm]
    exact commutator_mem_commutator a.property hvP
  rw [← hq, preimage_conjugate] at hz
  have hz' := (c.mem_preimage _ z).mp hz
  change (c.projection z).toAdd ∈ _ at hz'
  dsimp only [z] at hz'
  rw [map_mul, map_inv, toAdd_mul, toAdd_inv, ← sub_eq_add_neg,
    ← c.conjugationAction_projection, hv] at hz'
  exact hz'

theorem sylow_linear_of_small_plane_commutator
    (hNV : normalizer (V : Set G) ≤ normalizer (L : Set G))
    (A : Subgroup G) (hAT : A ≤ (T : Subgroup G)) (l : L)
    (hsmall : ⁅E.V₂, A⁆ ≤ E.V₁.map (MulAut.conj (l : G)).toMonoidHom)
    (a : A) :
    ∀ (t : E.input.field.Carrier) (v : F₀.action.coordinates.Space),
      F₀.action.coordinates.conjugationAction D.sylow_normalizes_component
        E.input.sylow_normalizes (inclusion hAT a) (t • v) =
          t • F₀.action.coordinates.conjugationAction D.sylow_normalizes_component
            E.input.sylow_normalizes (inclusion hAT a) v := by
  let c := F₀.action.coordinates
  obtain ⟨σ, hσ⟩ := sylow_semilinear F₀ hNV (inclusion hAT a)
  have : Finite c.Space := Finite.of_surjective
    (fun v : V => (c.projection v).toAdd) (fun x => by
      obtain ⟨v, hv⟩ := c.projection_surjective (Multiplicative.ofAdd x)
      exact ⟨v, congrArg Multiplicative.toAdd hv⟩)
  have : FiniteDimensional E.input.field.Carrier c.Space := Module.Finite.of_finite
  let e := LinearMap.GeneralLinearGroup.toLinearEquiv
    (c.modelAction.asGroupHom (c.quotientMap l))
  have hQ : Module.finrank E.input.field.Carrier
      ((F₀.flag.space 0).map (c.modelAction (c.quotientMap l))) = 1 := by
    change Module.finrank E.input.field.Carrier ((F₀.flag.space 0).map e.toLinearMap) = 1
    rw [e.finrank_map_eq]
    exact F₀.flag.dimension 0
  have he : σ = RingEquiv.refl E.input.field.Carrier := by
    apply PlaneDisplacement.field_twist_eq_one
      ((c.conjugationAction D.sylow_normalizes_component
        E.input.sylow_normalizes (inclusion hAT a)).toAddMonoidHom) σ hσ (F₀.flag.space 1)
      ((F₀.flag.space 0).map (c.modelAction (c.quotientMap l))) (F₀.flag.dimension 1) hQ
    exact displacement_mem_line F₀ A hAT l hsmall a
  simpa only [he, RingEquiv.refl_apply] using hσ

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.LineAlignment
