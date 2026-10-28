module

public import Theory.Representation.G2DerivedPermutationFiltration.VertexFiltrations.Transport
public import Theory.Representation.RepEquiv
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Factor-degree filtrations along exact maps

If an equivariant map has a filtered kernel and filtered codomain, its domain
has a filtration with the same allowed factor degrees. Pull back each step of
the codomain filtration. Its image in the last simple quotient is either zero,
when the step is omitted, or the whole quotient, when the first isomorphism
theorem identifies the literal new quotient with that simple factor.

This also proves closure under products. Applied to the actual incidence
boundary, it assembles the vertex and cycle filtrations of the binary G₂(2)′
flag module used for Aschbacher–Smith G.7.2(3), printed p.348 / PDF p.359.
-/

public section

namespace Representation.FactorDegreeFiltration

variable {k G U V W : Type*} [Field k] [Group G]
  [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]
  {τ : Representation k G U} {ρ : Representation k G V} {σ : Representation k G W}
  {D : Set ℕ}

/-- An injective kernel parametrization and a map to a filtered representation
assemble a filtration of the middle representation. The latter map need not
be surjective. -/
theorem of_exact (hτ : FactorDegreeFiltration D τ) (hσ : FactorDegreeFiltration D σ)
    (i : τ.IntertwiningMap ρ) (f : ρ.IntertwiningMap σ)
    (hi : Function.Injective i) (hex : ∀ v, f v = 0 ↔ ∃ u, i u = v) :
    FactorDegreeFiltration D ρ := by
  induction hσ generalizing V with
  | zero υ =>
    have his : Function.Surjective i := fun v => (hex v).mp (Subsingleton.elim _ _)
    apply hτ.transport (MonoidHom.id G) (fun g => ⟨g, rfl⟩) ρ
      (i.ofBijective ⟨hi, his⟩).toLinearEquiv
    intro g v
    exact LinearMap.congr_fun (i.isIntertwining' g) v
  | @step X _ _ υ S previous simple degree ih =>
    let q : υ.IntertwiningMap S.quotientRepresentation := {
      toLinearMap := S.toSubmodule.mkQ
      isIntertwining' := fun _ => rfl }
    let p := q.comp f
    let T := p.ker
    have hT (v : V) : v ∈ T ↔ f v ∈ S := by
      change S.toSubmodule.mkQ (f v) = 0 ↔ f v ∈ S.toSubmodule
      exact Submodule.Quotient.mk_eq_zero _
    let it : τ.IntertwiningMap T.toRepresentation := {
      toLinearMap := i.toLinearMap.codRestrict T.toSubmodule (by
        intro u
        apply (hT _).mpr
        have hf : f (i u) = 0 := (hex _).mpr ⟨u, rfl⟩
        change f (i u) ∈ S
        rw [hf]
        exact S.toSubmodule.zero_mem)
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro u
        apply Subtype.ext
        exact LinearMap.congr_fun (i.isIntertwining' g) u }
    let ft : T.toRepresentation.IntertwiningMap S.toRepresentation := {
      toLinearMap := (f.toLinearMap.comp T.toSubmodule.subtype).codRestrict
        S.toSubmodule (fun v => (hT v.val).mp v.property)
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro v
        apply Subtype.ext
        exact LinearMap.congr_fun (f.isIntertwining' g) v.val }
    have hit : Function.Injective it := by
      intro u v h
      exact hi (congrArg Subtype.val h)
    have hext (v : T.toSubmodule) : ft v = 0 ↔ ∃ u, it u = v := by
      constructor
      · intro h
        obtain ⟨u, hu⟩ := (hex v.val).mp (congrArg Subtype.val h)
        exact ⟨u, Subtype.ext hu⟩
      · rintro ⟨u, hu⟩
        apply Subtype.ext
        exact (hex v.val).mpr ⟨u, congrArg Subtype.val hu⟩
    have ht : FactorDegreeFiltration D T.toRepresentation := ih it ft hit hext
    by_cases hp : p = 0
    · let e : T.toSubmodule ≃ₗ[k] V := {
        toFun := Subtype.val
        invFun := fun v => ⟨v, by
          change p v = 0
          rw [hp]
          rfl⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
      apply ht.transport (MonoidHom.id G) (fun g => ⟨g, rfl⟩) ρ e
      intro g v
      rfl
    · let := simple
      have hps : Function.Surjective p :=
        (IsIrreducible.surjective_or_eq_zero p).resolve_right hp
      let e : T.quotientRepresentation.Equiv S.quotientRepresentation :=
        .mk (p.toLinearMap.quotKerEquivOfSurjective hps) (by
          intro g
          apply LinearMap.ext
          intro v
          induction v using Submodule.Quotient.induction_on with
          | H v => exact LinearMap.congr_fun (p.isIntertwining' g) v)
      refine .step T ht ((RepEquiv.ofRepresentationEquiv e).irreducible_of_euqiv simple) ?_
      rw [e.toLinearEquiv.finrank_eq]
      exact degree

/-- A filtered kernel and filtered codomain give a filtration of the domain. -/
theorem of_ker (f : ρ.IntertwiningMap σ)
    (hker : FactorDegreeFiltration D f.ker.toRepresentation)
    (hσ : FactorDegreeFiltration D σ) : FactorDegreeFiltration D ρ := by
  let i : f.ker.toRepresentation.IntertwiningMap ρ := {
    toLinearMap := f.ker.toSubmodule.subtype
    isIntertwining' := fun _ => rfl }
  apply of_exact hker hσ i f Subtype.val_injective
  intro v
  exact ⟨fun h => ⟨⟨v, h⟩, rfl⟩, fun ⟨u, hu⟩ => hu ▸ u.property⟩

/-- The product of two filtered representations has the same allowed degrees. -/
theorem prod (hρ : FactorDegreeFiltration D ρ) (hσ : FactorDegreeFiltration D σ) :
    FactorDegreeFiltration D (ρ.prod σ) := by
  apply of_exact hσ hρ (IntertwiningMap.inr k ρ σ) (IntertwiningMap.fst k ρ σ)
  · intro v w h
    exact congrArg Prod.snd h
  · intro v
    change v.1 = 0 ↔ ∃ w, (0, w) = v
    exact ⟨fun h => ⟨v.2, Prod.ext h.symm rfl⟩,
      fun ⟨w, h⟩ => (congrArg Prod.fst h).symm⟩

end Representation.FactorDegreeFiltration
