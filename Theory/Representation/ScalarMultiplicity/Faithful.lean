module
public import Theory.Representation.ScalarMultiplicity

/-!
# Faithful actions on a scalar multiplicity space

A commuting action on equal copies of a module with scalar commutant induces
an action on its multiplicity space. Pure tensors span the original space,
so a faithful action remains faithful after this reduction. This extends the
existing two-support construction to one homogeneous support.

Source application: the four-copy row of Aschbacher--Smith 10.1.1(6), p.741.
-/

public noncomputable section
namespace Representation.ScalarMultiplicity
variable {k F D C E I : Type*} [Field k] [Field F]
  [Group D] [Group C] [AddCommGroup E] [Module F E] [Module k E]
  [Nontrivial E] [Fintype I] [DecidableEq I]

theorem exists_injective_unit
    (σ : Representation k D E)
    (hs : ∀ (f : E →ₗ[k] E), (∀ d v, f (σ d v) = σ d (f v)) →
      ∃ c : F, ∀ v, f v = c • v)
    (ρ : Representation k C (I → E)) (hfaith : Function.Injective ρ)
    (hc : ∀ a d x, ρ a (fun i => σ d (x i)) = fun i => σ d (ρ a x i)) :
    ∃ f : C →* (Module.End F (I → F))ˣ, Function.Injective f := by
  obtain ⟨μ,he⟩ := exists_multiplicity σ hs ρ hc
  refine ⟨μ.asGroupHom,?_⟩
  intro a b hab
  apply hfaith
  apply LinearMap.ext
  intro x
  have hexp : x = ∑ i : I, Pi.single i (x i) := by ext i; simp
  rw [hexp,map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hsing (v : E) : (fun j => (Pi.single i (1 : F) : I → F) j • v) =
      Pi.single i v := by
    funext j
    by_cases h : i = j
    · subst j; simp
    · simp [Ne.symm h]
  have hh : μ a = μ b := congrArg Units.val hab
  rw [←hsing (x i),he,he,hh]

end Representation.ScalarMultiplicity
