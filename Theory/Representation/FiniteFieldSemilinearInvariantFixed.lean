module
public import Theory.Representation.HermitianTensorThree.ParabolicTorus.LargeFixed.FixedSpan
public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# Semilinear fixed vectors inside an invariant subspace

Restrict the original action to a field subspace U invariant under the
cyclic actor. If U contains all fixed vectors, the inclusion identifies
its cyclic fixed space with the original one. The coefficient order
therefore bounds fixed dimension using dim(U), rather than the dimension
of the whole module. No faithfulness of the coefficient action is needed.

The consumer is the four-dimensional fixed space of a saturated Hermitian
actor in H.4.4(4), Aschbacher–Smith, printed p.381, used in 8.2.3, p.716.
-/

public noncomputable section
open Module Subgroup Representation Representation.BinaryOffender
namespace Representation.FiniteFieldSemilinearDisplacement
variable {F G V : Type*} [Field F] [Algebra (ZMod 2) F] [Group G]
  [AddCommGroup V] [Module F V] [Module (ZMod 2) V] [IsScalarTower (ZMod 2) F V]
  [FiniteDimensional F V] [FiniteDimensional (ZMod 2) F]

/-- Restrict the coefficient-order estimate to an actual invariant field
subspace containing every fixed vector of the original actor. -/
theorem fixedSpace_order_bound_on_invariant
    (ρ : Representation (ZMod 2) G V) (x : G) (σ : F ≃ₐ[ZMod 2] F)
    (hsemi : ∀ (a : F) (v : V), ρ x (a • v) = σ a • ρ x v)
    (U : Submodule F V)
    (hU : zpowers x ≤ subspaceStabilizer ρ (U.restrictScalars (ZMod 2)))
    (hfixed : fixedSpace ρ (zpowers x) ≤ U.restrictScalars (ZMod 2)) :
    orderOf σ * finrank (ZMod 2) (fixedSpace ρ (zpowers x)) ≤
      finrank (ZMod 2) F * finrank F U := by
  let ψ : Representation (ZMod 2) (zpowers x) U :=
    { toFun := fun a =>
        { toFun := fun v => ⟨ρ a.val v.val, (hU a.property _).2 v.property⟩
          map_add' := fun v w => Subtype.ext ((ρ a.val).map_add v.val w.val)
          map_smul' := fun a v => Subtype.ext ((ρ _).map_smul a v.val) }
      map_one' := by ext v; exact LinearMap.congr_fun ρ.map_one v.val
      map_mul' := fun a b => by ext v; exact LinearMap.congr_fun (ρ.map_mul a.val b.val) v.val }
  let y : zpowers x := ⟨x,mem_zpowers x⟩
  have hsemi' (a : F) (v : U) : ψ y (a • v) = σ a • ψ y v := by
    apply Subtype.ext
    exact hsemi a v.val
  have hb := fixedSpace_order_bound (F := F) ψ y σ hsemi'
  let f : fixedSpace ψ (zpowers y) →ₗ[ZMod 2] fixedSpace ρ (zpowers x) :=
    { toFun := fun v => ⟨v.val.val, (mem_fixedSpace_zpowers_iff ρ x _).mpr
        (congrArg Subtype.val ((mem_fixedSpace_zpowers_iff ψ y _).mp v.property))⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hf : Function.Bijective f := by
    constructor
    · intro v w h
      exact Subtype.ext (Subtype.ext (congrArg (fun z => z.val) h))
    · intro v
      refine ⟨⟨⟨v.val,hfixed v.property⟩,?_⟩,rfl⟩
      apply (mem_fixedSpace_zpowers_iff ψ y _).mpr
      exact Subtype.ext ((mem_fixedSpace_zpowers_iff ρ x _).mp v.property)
  have he := (LinearEquiv.ofBijective f hf).finrank_eq
  rwa [he] at hb
end Representation.FiniteFieldSemilinearDisplacement

end
