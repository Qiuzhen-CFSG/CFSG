module

public import Theory.Representation.FactorDegreeFiltration

/-!
# Transporting actual factor-degree filtrations

An equivariant linear equivalence transports each invariant subspace and its
literal vector-space quotient. Surjectivity of the acting-group homomorphism
ensures that the transported subspaces are invariant under the whole target
group. Irreducibility and quotient dimensions then transport as well.

This is the assembly step connecting finite coordinate certificates to the
binary parabolic representations in Aschbacher–Smith G.7.2(3), printed p.348.
-/

@[expose] public section

namespace Representation.FactorDegreeFiltration

variable {k H G : Type*} [Field k] [Group H] [Group G]
  {V W : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

private theorem irreducible_transport
    {ρ : Representation k H V} {σ : Representation k G W}
    (f : H →* G) (e : V ≃ₗ[k] W)
    (he : ∀ g v, e (ρ g v) = σ (f g) (e v))
    [IsIrreducible ρ] : IsIrreducible σ := by
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  let : Nontrivial W := e.toEquiv.injective.nontrivial
  rw [IsIrreducible, isSimpleOrder_iff]
  refine ⟨inferInstance, fun S => ?_⟩
  let T : Subrepresentation ρ := {
    toSubmodule := S.toSubmodule.comap e.toLinearMap
    apply_mem_toSubmodule g v hv := by
      change e (ρ g v) ∈ S.toSubmodule
      rw [he]
      exact S.apply_mem_toSubmodule (f g) hv }
  rcases eq_bot_or_eq_top T with h | h
  · left
    apply le_antisymm _ bot_le
    intro w hw
    obtain ⟨v, rfl⟩ := e.surjective w
    have hv : v ∈ T := hw
    rw [h] at hv
    change v = 0 at hv
    change e v = 0
    rw [hv, map_zero]
  · right
    apply le_antisymm le_top
    intro w _
    obtain ⟨v, rfl⟩ := e.surjective w
    have hv : v ∈ T := by rw [h]; trivial
    exact hv

/-- Transport every invariant subspace and its literal quotient through an
equivariant linear equivalence and a surjective homomorphism of acting groups. -/
theorem transport {D : Set ℕ} {ρ : Representation k H V}
    (h : Representation.FactorDegreeFiltration D ρ)
    (f : H →* G) (hf : Function.Surjective f)
    (σ : Representation k G W) (e : V ≃ₗ[k] W)
    (he : ∀ g v, e (ρ g v) = σ (f g) (e v)) :
    Representation.FactorDegreeFiltration D σ := by
  induction h generalizing W with
  | zero τ =>
    let : Subsingleton W := e.symm.injective.subsingleton
    exact .zero σ
  | @step X _ _ τ S previous simple degree ih =>
    let T : Subrepresentation σ := {
      toSubmodule := S.toSubmodule.map e.toLinearMap
      apply_mem_toSubmodule g w hw := by
        obtain ⟨a, rfl⟩ := hf g
        obtain ⟨v, hv, rfl⟩ := hw
        exact ⟨τ a v, S.apply_mem_toSubmodule a hv, he a v⟩ }
    let es : S.toSubmodule ≃ₗ[k] T.toSubmodule := e.submoduleMap S.toSubmodule
    have hes : ∀ g v, es (S.toRepresentation g v) = T.toRepresentation (f g) (es v) := by
      intro g v
      apply Subtype.ext
      exact he g v.val
    let eq : (X ⧸ S.toSubmodule) ≃ₗ[k] (W ⧸ T.toSubmodule) :=
      Submodule.Quotient.equiv S.toSubmodule T.toSubmodule e rfl
    have heq : ∀ g v, eq (S.quotientRepresentation g v) =
        T.quotientRepresentation (f g) (eq v) := by
      intro g v
      induction v using Submodule.Quotient.induction_on with
      | H v => exact congrArg T.toSubmodule.mkQ (he g v)
    refine .step T (ih T.toRepresentation es hes) ?_ ?_
    · let := simple
      exact irreducible_transport f eq heq
    · rw [← eq.finrank_eq]
      exact degree

end Representation.FactorDegreeFiltration
