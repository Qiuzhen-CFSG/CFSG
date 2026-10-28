module

public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.SolvableCoordinates
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model

/-!
# The one-factor binary natural quotient

With one factor, the actual moved module is a binary plane. Its faithful
ambient action gives a homomorphism into GL₂(2)=SL₂(2), and the original
natural factor makes that map surjective. The maps below preserve the
original action and the exact residual fixed-space kernel.

Source: Aschbacher–Smith B.6.9 and E.2.3(2), printed pp.115–117,216–217.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SolvableFFFactors
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} (d : SolvableFFFactors ρ)

noncomputable def singleActorCoordinates (hc : d.count = 1) :
    offenderSubgroup ρ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) :=
  (d.naturalActorCoordinates.trans
    (MulEquiv.arrowCongr (finCongr hc) (MulEquiv.refl _))).trans
      { toEquiv := Equiv.funUnique (Fin 1) _
        map_mul' _ _ := rfl }

noncomputable def singleSpaceCoordinates (hc : d.count = 1) :
    (Fin d.count → Fin 2 → ZMod 2) ≃ₗ[ZMod 2] (Fin 2 → ZMod 2) :=
  (LinearEquiv.piCongrLeft' (ZMod 2) (fun _ : Fin d.count => Fin 2 → ZMod 2)
    (finCongr hc)).trans (LinearEquiv.funUnique (Fin 1) (ZMod 2) _)

noncomputable def singleMovedAction (hc : d.count = 1) :
    Representation (ZMod 2) G (Fin 2 → ZMod 2) :=
  (d.singleSpaceCoordinates hc).conjRingEquiv.toMonoidHom.comp d.naturalMovedAction

noncomputable def singleQuotientMap [Finite G] [FiniteDimensional (ZMod 2) V]
    (hf : Function.Injective ρ) (hr : pResidual 2 G ≤ offenderSubgroup ρ)
    (hc : d.count = 1) : V →ₗ[ZMod 2] (Fin 2 → ZMod 2) :=
  (d.singleSpaceCoordinates hc).toLinearMap.comp (d.naturalQuotientMap hf hr)

theorem singleMovedAction_natural (hc : d.count = 1) (g : offenderSubgroup ρ)
    (v : Fin 2 → ZMod 2) :
    d.singleMovedAction hc g v = (d.singleActorCoordinates hc g).val.mulVec v := by
  change d.singleSpaceCoordinates hc (d.naturalMovedAction g ((d.singleSpaceCoordinates hc).symm v)) = _
  rw [d.naturalMovedAction_natural]
  rfl

theorem singleQuotientMap_surjective [Finite G] [FiniteDimensional (ZMod 2) V]
    (hf : Function.Injective ρ) (hr : pResidual 2 G ≤ offenderSubgroup ρ)
    (hc : d.count = 1) : Function.Surjective (d.singleQuotientMap hf hr hc) :=
  (d.singleSpaceCoordinates hc).surjective.comp (d.naturalQuotientMap_surjective hf hr)

theorem singleQuotientMap_equivariant [Finite G] [FiniteDimensional (ZMod 2) V]
    (hf : Function.Injective ρ) (hr : pResidual 2 G ≤ offenderSubgroup ρ)
    (hc : d.count = 1) (g : G) (v : V) :
    d.singleQuotientMap hf hr hc (ρ g v) =
      d.singleMovedAction hc g (d.singleQuotientMap hf hr hc v) := by
  change d.singleSpaceCoordinates hc (d.naturalQuotientMap hf hr (ρ g v)) =
    d.singleSpaceCoordinates hc (d.naturalMovedAction g
      ((d.singleSpaceCoordinates hc).symm (d.singleSpaceCoordinates hc (d.naturalQuotientMap hf hr v))))
  rw [LinearEquiv.symm_apply_apply, d.naturalQuotientMap_equivariant]

theorem singleMovedAction_injective [Finite G] (hf : Function.Injective ρ)
    (hcore : pCore 2 G = ⊥) (hr : pResidual 2 G ≤ offenderSubgroup ρ)
    (hc : d.count = 1) : Function.Injective (d.singleMovedAction hc) :=
  (d.singleSpaceCoordinates hc).conjRingEquiv.injective.comp
    (d.naturalMovedAction_injective hf hcore hr)

theorem singleQuotientMap_ker [Finite G] [FiniteDimensional (ZMod 2) V]
    (hf : Function.Injective ρ) (hr : pResidual 2 G ≤ offenderSubgroup ρ)
    (hc : d.count = 1) : (d.singleQuotientMap hf hr hc).ker = fixedSpace ρ (pResidual 2 G) := by
  rw [d.fixed_residual_eq hf hr]
  ext v
  change d.singleSpaceCoordinates hc (d.naturalQuotientMap hf hr v) = 0 ↔ _
  rw [LinearEquiv.map_eq_zero_iff]
  exact iff_of_eq (congrArg (fun W : Submodule (ZMod 2) V => v ∈ W) (d.naturalQuotientMap_ker hf hr))

noncomputable def singleAmbientHom (hc : d.count = 1) :
    G →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) :=
  (BinaryLinear.OuterCyclic.slEquivLinear 2).symm.toMonoidHom.comp
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin 2 → ZMod 2)).toMonoidHom.comp
      (d.singleMovedAction hc).asGroupHom)

theorem singleAmbientHom_action (hc : d.count = 1) (g : G) (v : Fin 2 → ZMod 2) :
    (d.singleAmbientHom hc g).val.mulVec v = d.singleMovedAction hc g v := by
  change (BinaryLinear.OuterCyclic.slEquivLinear 2 (d.singleAmbientHom hc g)) v = _
  rw [singleAmbientHom,MonoidHom.comp_apply,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply]
  rfl

theorem singleAmbientHom_factor (hc : d.count = 1) (g : offenderSubgroup ρ) :
    d.singleAmbientHom hc g = d.singleActorCoordinates hc g := by
  apply Matrix.SpecialLinearGroup.toLin'_injective
  apply LinearEquiv.ext
  intro v
  exact (d.singleAmbientHom_action hc g v).trans (d.singleMovedAction_natural hc g v)

theorem singleAmbientHom_surjective (hc : d.count = 1) :
    Function.Surjective (d.singleAmbientHom hc) := by
  intro a
  obtain ⟨g,rfl⟩ := (d.singleActorCoordinates hc).surjective a
  exact ⟨g,d.singleAmbientHom_factor hc g⟩

theorem singleAmbientHom_injective [Finite G] (hf : Function.Injective ρ)
    (hcore : pCore 2 G = ⊥) (hr : pResidual 2 G ≤ offenderSubgroup ρ)
    (hc : d.count = 1) : Function.Injective (d.singleAmbientHom hc) := by
  intro g h he
  apply d.singleMovedAction_injective hf hcore hr hc
  apply LinearMap.ext
  intro v
  rw [← d.singleAmbientHom_action hc g v,← d.singleAmbientHom_action hc h v,he]

end CFSG.Quasithin.ChapterB.SolvableFFFactors
