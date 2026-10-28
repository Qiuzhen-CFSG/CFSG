module
public import Theory.Representation.BinaryAlternatingFiveFixedPoint.Splitting

/-!
# Whole deleted-module coordinates after canonical splitting

If the complement of the deleted A₅ type is zero, the full module is its
isotypic component. Finite-dimensional isotypic coordinates give a finite
number of copies with the same actor on every copy. Semisimplicity follows
from this proved identification, rather than being a premise.

This is the whole-layer decomposition step of Aschbacher--Smith 5.1.14(4)
and 5.1.19, printed pp.638,643--644.
-/

public noncomputable section
open Representation Module
open scoped MonoidAlgebra
namespace Representation.BinaryAlternatingFiveFixedPoint
open BinaryPermutation
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- When the canonical complement vanishes, the entire module has finite
copy coordinates with the same original A₅ acting in every coordinate. -/
theorem exists_core_coordinates_of_typeReject_eq_bot
    (ρ : Representation (ZMod 2) A5 V)
    (hR : Representation.typeReject ρ (alternatingCoreRepresentation (Fin 5)) = ⊥) :
    ∃ k : ℕ, ∃ c : V ≃ₗ[ZMod 2] (Fin k → core (Fin 5)),
      ∀ g v, c (ρ g v) = fun i => alternatingCoreRepresentation (Fin 5) g (c v i) := by
  let σ := alternatingCoreRepresentation (Fin 5)
  let e : σ ≃ₗ alternatingNaturalRepresentation (Fin 5) :=
    .mk (coreEquivNatural (Fin 5) (by decide)) (by
      intro g
      apply LinearMap.ext
      intro v
      exact coreEquivNatural_equivariant (Fin 5) (by decide) g.val v)
  let : σ.IsIrreducible :=
    e.irreducible_of_euqiv (alternatingNatural_isIrreducible (by decide))
  have htop := (isCompl_core_typeSpan_typeReject ρ).sup_eq_top
  rw [hR, sup_bot_eq, NormalPairHomogeneous.typeSpan_eq_isotypic] at htop
  let S := Subrepresentation.ofSubmodule'
    (isotypicComponent (ZMod 2)[A5] ρ.asModule σ.asModule)
  have hS : S.toSubmodule = ⊤ := congrArg Subrepresentation.toSubmodule htop
  let a : V ≃ₗ[ZMod 2] S.toSubmodule := LinearEquiv.ofBijective
    (LinearMap.codRestrict S.toSubmodule (LinearMap.id : V →ₗ[ZMod 2] V)
      (fun v => hS ▸ Submodule.mem_top)) ⟨fun _ _ h => congrArg Subtype.val h,
      fun v => ⟨v.val,Subtype.ext rfl⟩⟩
  obtain ⟨k,c,hc⟩ := SchurCopies.isotypic_finite_rep_coordinates ρ σ
  exact ⟨k,a.trans c,fun g v => hc g (a v)⟩

/-- The same whole-module coordinates in the public deleted quotient model. -/
theorem exists_natural_coordinates_of_typeReject_eq_bot
    (ρ : Representation (ZMod 2) A5 V)
    (hR : Representation.typeReject ρ (alternatingCoreRepresentation (Fin 5)) = ⊥) :
    ∃ k : ℕ, ∃ c : V ≃ₗ[ZMod 2] (Fin k → natural (Fin 5)),
      ∀ g v, c (ρ g v) = fun i => alternatingNaturalRepresentation (Fin 5) g (c v i) := by
  obtain ⟨k,c,hc⟩ := exists_core_coordinates_of_typeReject_eq_bot ρ hR
  let d := coreEquivNatural (Fin 5) (by decide)
  refine ⟨k,c.trans (LinearEquiv.piCongrRight fun _ => d),?_⟩
  intro g v
  change (fun i => d (c (ρ g v) i)) = _
  rw [hc]
  funext i
  exact coreEquivNatural_equivariant (Fin 5) (by decide) g.val (c v i)
/-- Vanishing of the canonical complement proves semisimplicity of the
entire representation, rather than assuming it as a splitting premise. -/
theorem semisimple_of_typeReject_eq_bot
    (ρ : Representation (ZMod 2) A5 V)
    (hR : Representation.typeReject ρ (alternatingCoreRepresentation (Fin 5)) = ⊥) :
    IsSemisimpleModule (ZMod 2)[A5] ρ.asModule := by
  let σ := alternatingCoreRepresentation (Fin 5)
  let e : σ ≃ₗ alternatingNaturalRepresentation (Fin 5) :=
    .mk (coreEquivNatural (Fin 5) (by decide)) (by
      intro g
      apply LinearMap.ext
      intro v
      exact coreEquivNatural_equivariant (Fin 5) (by decide) g.val v)
  let : σ.IsIrreducible :=
    e.irreducible_of_euqiv (alternatingNatural_isIrreducible (by decide))
  have htop := (isCompl_core_typeSpan_typeReject ρ).sup_eq_top
  rw [hR, sup_bot_eq, NormalPairHomogeneous.typeSpan_eq_isotypic] at htop
  have ht : isotypicComponent (ZMod 2)[A5] ρ.asModule σ.asModule = ⊤ :=
    congrArg Subrepresentation.asSubmodule htop
  let S := isotypicComponent (ZMod 2)[A5] ρ.asModule σ.asModule
  apply IsSemisimpleModule.of_surjective S.subtype
  intro v
  exact ⟨⟨v,ht.ge Submodule.mem_top⟩,rfl⟩

end Representation.BinaryAlternatingFiveFixedPoint
