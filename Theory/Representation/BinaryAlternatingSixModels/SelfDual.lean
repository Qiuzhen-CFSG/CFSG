module
public import Theory.Representation.BinaryAlternatingSixModels.CatalogueSource
public import Theory.Representation.BinaryDuadStructure.OppositeCover.Geometry

/-!
# Self-duality of the binary A₆ catalogue

Each of the four literal irreducible models has an invariant perfect pairing.
Transporting its equivariant self-duality through the actual catalogue
isomorphism preserves the given component action, without an outer twist.
Source: Aschbacher--Smith G.5.1--2 and G.11.6, pp.342--343,365--366.
-/

public noncomputable section
open Theory.SpecificGroups.SymmetricSix Representation
namespace BinaryAlternatingSix

private def trivialSelfDual : trivialAlternating.Equiv trivialAlternating.dual :=
  .mk (LinearMap.ringLmapEquivSelf (ZMod 2) (ZMod 2) (ZMod 2)).symm
    (by intro g; apply LinearMap.ext; intro x; apply LinearMap.ext; intro y; rfl)

private def firstSelfDual : firstAlternating.Equiv firstAlternating.dual :=
  .mk (polarForm.toDual polarForm_nondegenerate) (by
    intro g
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    change polarForm (polarAction g.val v) w = polarForm v (polarAction g⁻¹.val w)
    have he : polarAction g.val (polarAction g⁻¹.val w) = w := by
      rw [← polarAction_mul]
      change polarAction (g.val * g.val⁻¹) w = w
      simp
    rw [← he, polarAction_form]
    rw [he])

private def tensorSelfDual : Representation.Equiv alternatingTensor (Representation.dual alternatingTensor) :=
  .mk SymmetricCatalogue.tensorSelfDualEquiv.toLinearEquiv
    (fun g => SymmetricCatalogue.tensorSelfDualEquiv.isIntertwining' g.val)

private def transportSelfDual {D V W : Type*} [Group D]
    [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) D V} {σ : Representation (ZMod 2) D W}
    (e : ρ.Equiv σ) (d : σ.Equiv σ.dual) : ρ.Equiv ρ.dual :=
  (e.trans d).trans (.mk e.toLinearEquiv.dualMap (by
    intro g
    ext f v
    exact congrArg f (LinearMap.congr_fun (e.isIntertwining' g⁻¹) v).symm))

/-- Every irreducible binary A₆ representation is self-dual for its fixed action. -/
theorem alternating_selfDual {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) A6 V)
    [IsIrreducible ρ] : Nonempty (ρ.Equiv ρ.dual) := by
  rcases alternating_classify ρ with he | he | he | he
  all_goals obtain ⟨e⟩ := he
  · exact ⟨transportSelfDual e trivialSelfDual⟩
  · exact ⟨transportSelfDual e firstSelfDual⟩
  · exact ⟨transportSelfDual e BinaryDuadStructure.OppositeCover.secondSelfDual⟩
  · exact ⟨transportSelfDual e tensorSelfDual⟩

/-- An actual component marking transports self-duality back to the original
representation, with no change of the component's action. -/
theorem selfDual_of_alternatingSix_equiv {D V : Type*} [Group D]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) [IsIrreducible ρ]
    (e : D ≃* alternatingGroup (Fin 6)) : Nonempty (ρ.Equiv ρ.dual) := by
  let σ := ρ.comp e.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective ρ).mpr inferInstance
  obtain ⟨d⟩ := alternating_selfDual σ
  refine ⟨.mk d.toLinearEquiv ?_⟩
  intro g
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  have h := congrArg (fun z : V →ₗ[ZMod 2] Module.Dual (ZMod 2) V => z x y)
    (d.isIntertwining' (e g))
  change d (ρ (e.symm (e g)) x) y = d x (ρ (e.symm ((e g)⁻¹)) y) at h
  change d (ρ g x) y = d x (ρ g⁻¹ y)
  simpa only [map_inv, e.symm_apply_apply] using h

end BinaryAlternatingSix
