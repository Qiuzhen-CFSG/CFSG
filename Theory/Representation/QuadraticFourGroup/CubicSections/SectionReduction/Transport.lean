module

public import Theory.Representation.QuadraticFourGroup.CubicSections.SplitSection
public import Theory.Representation.QuadraticFourGroup.CubicSections.Descent
public import Theory.Representation.kerRepresentation

/-!
# Compatible faithful quotients for orbit sections

An actual invariant subquotient kills the kernel of the original action.
A normal two-core also kills an irreducible ambient binary action. Given
that containment, the supplied two-factor model defines a canonical map
into the faithful kernel quotient. Its kernel is trivial precisely when
the restricted ambient kernel is the two-core. Surjective inflation then
puts the prescribed descended section in the restriction of that action.

These are the transport steps in GLS, volume 2, Theorem 25.14, Step 2.
They do not assert the existence of the ambient irreducible section or
the exact kernel equality.
-/

@[expose] public section

open Subgroup Theory.GroupTheory

namespace Representation.QuadraticFourGroup

section Sections
variable {k G V W : Type*} [Field k] [Group G]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  {ρ : Representation k G V} {σ : Representation k G W}

theorem IsIrreducibleSection.ker_le (hs : IsIrreducibleSection ρ σ) : ρ.ker ≤ σ.ker := by
  obtain ⟨_, U, N, ⟨e⟩⟩ := hs
  intro g hg
  have hU : U.toRepresentation g = 1 := by
    ext v
    exact congrArg (fun f : Module.End k V => f v) hg
  have hN : N.quotientRepresentation g = 1 := by
    apply LinearMap.ext
    intro v
    induction v using Submodule.Quotient.induction_on with
    | _ v =>
      change N.toSubmodule.mkQ (U.toRepresentation g v) = N.toSubmodule.mkQ v
      rw [hU]
      rfl
  apply LinearMap.ext
  intro w
  obtain ⟨v, rfl⟩ := e.toLinearEquiv.surjective w
  have he := congrArg (fun f => f v) (e.isIntertwining' g)
  rw [hN] at he
  exact he.symm

theorem IsIrreducibleSection.isTrivial (hs : IsIrreducibleSection ρ σ)
    (hρ : ρ.IsTrivial) : σ.IsTrivial :=
  ⟨fun g => hs.ker_le (hρ.out g)⟩

end Sections

section Displacements
variable {k G Q V : Type*} [Field k] [Group G] [Group Q]
  [AddCommGroup V] [Module k V]
  {τ : Representation k Q V} {a : G} {B : Subgroup G}

theorem FixesDisplacements.image (f : G →* Q)
    (h : FixesDisplacements (τ.comp f) a B) :
    FixesDisplacements τ (f a) (B.map f) := by
  rintro _ ⟨b, hb, rfl⟩ v
  exact h b hb v

end Displacements

namespace TwoFactorModel
variable {E Q : Type*} [Group E] [Group Q] (M : TwoFactorModel E)
  (f : E →* Q) (hf : pCore 2 E ≤ f.ker)

/-- Lift through the given model, retaining its specific quotient equivalence. -/
noncomputable def liftTo : Factor M.n × Factor M.n →* Q :=
  (QuotientGroup.lift (pCore 2 E) f hf).comp M.quotientEquiv.symm.toMonoidHom

@[simp] theorem liftTo_projection (x : E) : M.liftTo f hf (M.projection x) = f x := by
  simp only [liftTo, projection, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply]
  rfl

theorem liftTo_comp_projection : (M.liftTo f hf).comp M.projection = f := by
  ext x
  exact M.liftTo_projection f hf x

theorem liftTo_injective (hker : f.ker = pCore 2 E) :
    Function.Injective (M.liftTo f hf) :=
  ((QuotientGroup.injective_lift_iff _ f hf).mpr hker.symm).comp
    M.quotientEquiv.symm.injective

theorem liftTo_range : (M.liftTo f hf).range = f.range := by
  calc
    (M.liftTo f hf).range = ((M.liftTo f hf).comp M.projection).range := by
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective M.projection
        M.projection_surjective, ← MonoidHom.range_eq_map]
    _ = f.range := congrArg MonoidHom.range (M.liftTo_comp_projection f hf)

end TwoFactorModel

namespace SectionReduction

section NormalCore
variable {G U : Type*} [Group G] [Finite G]
  [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]

/-- The core of a normal subgroup kills every irreducible ambient binary action. -/
theorem normal_twoCore_le_ker (τ : Representation (ZMod 2) G U) [τ.IsIrreducible]
    (E : Subgroup G) [E.Normal] : pCore 2 E ≤ (τ.comp E.subtype).ker := by
  have hk := normal_p_subgroup_le_ker τ ((pCore 2 E).map E.subtype)
    (pCore_isPGroup.map E.subtype)
  intro x hx
  exact hk (mem_map_of_mem E.subtype hx)

end NormalCore

section FaithfulImage
variable {E X U W : Type*} [Group E] [Group X]
  [AddCommGroup U] [Module (ZMod 2) U]
  [AddCommGroup W] [Module (ZMod 2) W]
  (i : E →* X) (τ : Representation (ZMod 2) X U) (M : TwoFactorModel E)

theorem quotient_restriction_ker :
    ((QuotientGroup.mk' τ.ker).comp i).ker = (τ.comp i).ker := by
  rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', MonoidHom.comap_ker]

/-- The canonical map into the faithful quotient; injectivity needs exact kernel equality. -/
noncomputable def embedding (hk : pCore 2 E ≤ (τ.comp i).ker) :
    Factor M.n × Factor M.n →* X ⧸ τ.ker :=
  M.liftTo ((QuotientGroup.mk' τ.ker).comp i)
    (by rwa [quotient_restriction_ker])

@[simp] theorem embedding_projection (hk : pCore 2 E ≤ (τ.comp i).ker) (x : E) :
    embedding i τ M hk (M.projection x) = QuotientGroup.mk' τ.ker (i x) :=
  M.liftTo_projection _ _ x

theorem embedding_injective (hk : pCore 2 E ≤ (τ.comp i).ker)
    (hker : (τ.comp i).ker = pCore 2 E) : Function.Injective (embedding i τ M hk) :=
  M.liftTo_injective _ _ ((quotient_restriction_ker i τ).trans hker)

theorem faithfulAction_comp_embedding (hk : pCore 2 E ≤ (τ.comp i).ker) :
    ((kerRepresentation τ).comp (embedding i τ M hk)).comp M.projection = τ.comp i := by
  ext x u
  change kerRepresentation τ (embedding i τ M hk (M.projection x)) u = τ (i x) u
  rw [embedding_projection, kerRepresentation_apply]

/-- The prescribed descended section occurs in the faithful quotient restriction. -/
theorem faithfulAction_isSection (hk : pCore 2 E ≤ (τ.comp i).ker)
    [Finite E] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) E W) (hs : IsIrreducibleSection (τ.comp i) σ) :
    letI := hs.1
    IsIrreducibleSection ((kerRepresentation τ).comp (embedding i τ M hk))
      (M.sectionRepresentation σ) := by
  let := hs.1
  apply IsIrreducibleSection.of_comp_surjective M.projection M.projection_surjective
  rw [faithfulAction_comp_embedding, M.sectionRepresentation_comp]
  exact hs

end FaithfulImage

end SectionReduction
end Representation.QuadraticFourGroup

end
