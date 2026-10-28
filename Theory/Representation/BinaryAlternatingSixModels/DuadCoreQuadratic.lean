module

public import Theory.Representation.BinaryAlternatingSixModels
public import Theory.Representation.BinaryOffender.Defs
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad.Calculation
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad.Models

/-!
# The literal duad eight-group is not quadratic on the first natural module

The two double transpositions on the complementary letters `{2,3,4,5}`
have a nonzero second displacement on the vector of the duad `{0,2}`.
This proves the obstruction in the original `{0,1}` marking. Equivariant
transport and inner conjugation preserve the same obstruction.

Source: Aschbacher–Smith, proof of 13.5.7, printed pp.917–918, and the
duad two-core of I.5.7, printed pp.420–421.
-/

public section

namespace BinaryAlternatingSix
open Theory.SpecificGroups.SymmetricSix Representation.BinaryOffender
open DuadCalculation

private def actorA : S6 := duadProductHom (1, doubleSwap 0)
private def actorB : S6 := duadProductHom (1, doubleSwap 1)

private theorem actorA_mem : actorA ∈ productCore.map duadProductHom := by
  refine ⟨(1, doubleSwap 0), ⟨Subgroup.mem_top _, ?_⟩, rfl⟩
  change quotientHom (doubleSwap 0) = 1
  decide

private theorem actorB_mem : actorB ∈ productCore.map duadProductHom := by
  refine ⟨(1, doubleSwap 1), ⟨Subgroup.mem_top _, ?_⟩, rfl⟩
  change quotientHom (doubleSwap 1) = 1
  decide

private theorem actorA_one : firstNatural actorA (polarVector 1).val =
    (polarVector 2).val := by
  change polarAction actorA (polarVector 1).val = _
  rw [polarAction_vector]
  apply congrArg (fun d => (polarVector d).val)
  apply duadSet_injective
  rw [duadSet_smul]
  decide

private theorem actorA_three : firstNatural actorA (polarVector 3).val =
    (polarVector 4).val := by
  change polarAction actorA (polarVector 3).val = _
  rw [polarAction_vector]
  apply congrArg (fun d => (polarVector d).val)
  apply duadSet_injective
  rw [duadSet_smul]
  decide

private theorem actorB_one : firstNatural actorB (polarVector 1).val =
    (polarVector 3).val := by
  change polarAction actorB (polarVector 1).val = _
  rw [polarAction_vector]
  apply congrArg (fun d => (polarVector d).val)
  apply duadSet_injective
  rw [duadSet_smul]
  decide

/-- The original duad eight-group has a nonzero second displacement. -/
theorem firstNatural_not_quadratic_duadCore :
    ¬ IsQuadratic firstNatural (productCore.map duadProductHom) := by
  intro hq
  have h := hq actorA actorA_mem actorB actorB_mem (polarVector 1).val
  rw [map_sub, actorB_one, actorA_three, actorA_one] at h
  exact (by decide : (polarVector 4).val - (polarVector 2).val ≠
    (polarVector 3).val - (polarVector 1).val) h

/-- Equivariant coordinates retaining the literal duad-core image exclude
quadraticity on the entire source module. No injectivity of the actor map
or quotient of the module is required. -/
theorem not_quadratic_of_duadCore_marking {G V : Type*} [Group G]
    [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) G V) (f : G →* S6)
    (E : V ≃ₗ[ZMod 2] NaturalModule)
    (hE : ∀ g v, E (σ g v) = firstNatural (f g) (E v))
    (A : Subgroup G) (hA : A.map f = productCore.map duadProductHom) :
    ¬ IsQuadratic σ A := by
  intro hq
  apply firstNatural_not_quadratic_duadCore
  rw [← hA]
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ w
  obtain ⟨v, rfl⟩ := E.surjective w
  have h := congrArg E (hq a ha b hb v)
  simpa only [hE, map_sub] using h

/-- An inner marking of the actor retains the obstruction for any module
equivalent to the first natural representation. -/
theorem not_quadratic_of_equiv_firstNatural_of_conjugate_duadCore
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) S6 V) (e : σ.Equiv firstNatural)
    (A : Subgroup S6) (g : S6)
    (hA : A.map (MulAut.conj g).toMonoidHom = productCore.map duadProductHom) :
    ¬ IsQuadratic σ A := by
  let E := e.toLinearEquiv.trans
    (LinearMap.GeneralLinearGroup.toLinearEquiv (firstNatural.asGroupHom g))
  apply not_quadratic_of_duadCore_marking σ (MulAut.conj g).toMonoidHom E _ A hA
  intro a v
  change firstNatural g (e (σ a v)) =
    firstNatural (g * a * g⁻¹) (firstNatural g (e v))
  have he : e (σ a v) = firstNatural a (e v) :=
    Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap a v
  rw [he]
  simp only [map_mul, Module.End.mul_apply, firstNatural.inv_self_apply]

end BinaryAlternatingSix
