module
public import Theory.Representation.BinaryOffender.Homogeneous.FaithfulOrbit
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.EquivariantStabilizer
public import Theory.Representation.BinaryOffender.IrreducibleOrbitGeometry

/-!
# FF transport for the literal moved seed

The original stabilizer maps onto the stabilizer of the seed inside an
invariant containing space. Restriction through that space therefore has
the same faithful seed image. Conjugation by an actual representation
operator likewise identifies the actions on a seed and its translate.
Both arguments transport offenders using explicit equivariant maps.

These supply the coordinate changes in D.3.5(2), printed pp.195--196,
Aschbacher--Smith, combined manuscript of 1 March 2004. The chosen-module
consumer is `SeedAlternativesMovedActor`.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
variable {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) H W)

/-- Passage through a containing invariant space does not change the faithful
seed action or its FF property. The map is induced by the original inclusion. -/
theorem isFFModule_of_nested_image
    (U I : Submodule (ZMod 2) W)
    (hU : (⊤ : Subgroup H) ≤ subspaceStabilizer ρ U) (hIU : I ≤ U)
    (hff : IsFFModule (subspaceImageRepresentation (subspaceImageRepresentation ρ U)
      (I.comap U.subtype))) : IsFFModule (subspaceImageRepresentation ρ I) := by
  let σ := subspaceImageRepresentation ρ U
  let J := I.comap U.subtype
  let f := invariantActionHom ρ U hU
  have hs (g : H) : g ∈ subspaceStabilizer ρ I ↔ f g ∈ subspaceStabilizer σ J := by
    constructor
    · intro hg v
      change (σ (f g) v : W) ∈ I ↔ (v : W) ∈ I
      rw [invariantActionHom_apply]
      exact hg v
    · intro hg v
      constructor
      · intro hv
        have hvU : v ∈ U := (hU (mem_top g) v).1 (hIU hv)
        have he := (hg (⟨v,hvU⟩ : U)).1
        apply he
        change (σ (f g) ⟨v,hvU⟩ : W) ∈ I
        rwa [invariantActionHom_apply]
      · intro hv
        have he := (hg (⟨v,hIU hv⟩ : U)).2 hv
        change (σ (f g) ⟨v,hIU hv⟩ : W) ∈ I at he
        rwa [invariantActionHom_apply] at he
  let q : subspaceStabilizer ρ I →* subspaceStabilizer σ J :=
    { toFun := fun g => ⟨f g,(hs g).mp g.property⟩
      map_one' := Subtype.ext f.map_one
      map_mul' := fun g k => Subtype.ext (f.map_mul g k) }
  have hq : Function.Surjective q := by
    intro g
    obtain ⟨x,hx⟩ := invariantActionHom_surjective ρ U hU g.val
    exact ⟨⟨x,(hs x).mpr (hx.symm ▸ g.property)⟩,Subtype.ext hx⟩
  let E : J ≃ₗ[ZMod 2] I := Submodule.comapSubtypeEquivOfLe hIU
  apply image_isFFModule_of_equivariant (stabilizerRepresentation ρ I)
    (stabilizerRepresentation σ J) q hq E _ hff
  intro g v
  apply Subtype.ext
  exact (invariantActionHom_apply ρ U hU g v.val).symm

/-- Conjugation by an actual representation operator transports the full
stabilizer action, and therefore transports an FF offender to the seed. -/
theorem isFFModule_of_conjugate_image (I : Submodule (ZMod 2) W) (a : H)
    (hff : IsFFModule (subspaceImageRepresentation ρ (I.map (ρ a)))) :
    IsFFModule (subspaceImageRepresentation ρ I) := by
  let e := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W (ρ.asGroupHom a)
  let f := MulAut.conj a
  have he (g : H) (v : W) : e (ρ g v) = ρ (f g) (e v) := by
    change ρ a (ρ g v) = ρ (a * g * a⁻¹) (ρ a v)
    simp only [← Module.End.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel, mul_one]
  have hs (g : H) : g ∈ subspaceStabilizer ρ I ↔
      f g ∈ subspaceStabilizer ρ (I.map (ρ a)) :=
    mem_subspaceStabilizer_equivariant ρ ρ f e he I g
  let q : subspaceStabilizer ρ I →* subspaceStabilizer ρ (I.map (ρ a)) :=
    { toFun := fun g => ⟨f g,(hs g).mp g.property⟩
      map_one' := Subtype.ext f.map_one
      map_mul' := fun g k => Subtype.ext (f.map_mul g k) }
  have hq : Function.Surjective q := by
    intro g
    refine ⟨⟨f.symm g, (hs _).mpr ?_⟩,Subtype.ext (f.apply_symm_apply g)⟩
    simpa only [f.apply_symm_apply] using g.property
  let E : I ≃ₗ[ZMod 2] I.map (ρ a) := e.submoduleMap I
  apply image_isFFModule_of_equivariant (stabilizerRepresentation ρ I)
    (stabilizerRepresentation ρ (I.map (ρ a))) q hq E.symm _ hff
  intro g v
  apply E.injective
  have hx : E ((stabilizerRepresentation ρ I g) (E.symm v)) =
      (stabilizerRepresentation ρ (I.map (ρ a)) (q g)) v := by
    apply Subtype.ext
    exact (he g (E.symm v)).trans
      (congrArg (ρ (f g)) (congrArg Subtype.val (E.apply_symm_apply v)))
  rw [E.apply_symm_apply]
  exact hx

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
