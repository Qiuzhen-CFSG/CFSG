module
public import Theory.Representation.ScalarMultiplicity
/-!
# The full kernel of a scalar multiplicity action

Pure tensors span a finite family of equal modules. Consequently the
multiplicity action constructed from a scalar commutant has exactly the
same kernel as the original action, even when that action is not faithful.
This retains the original quotient map when passing to a faithful action
on the multiplicity coordinates.

Source application: Aschbacher–Smith 8.2.8(3–5), printed pp.718–719,
refs/quasithin.pdf (1 March 2004 manuscript).
-/

public noncomputable section
namespace Representation.ScalarMultiplicity
variable {k F D C E I : Type*} [Field k] [Field F]
  [Group D] [Group C] [AddCommGroup E] [Module F E] [Module k E]
  [Nontrivial E] [Fintype I] [DecidableEq I]

/-- Multiplicity coordinates preserve the full action kernel and the pure-tensor formula. -/
theorem exists_multiplicity_kernel
    (σ : Representation k D E)
    (hs : ∀ (f : E →ₗ[k] E), (∀ d v, f (σ d v) = σ d (f v)) →
      ∃ c : F, ∀ v, f v = c • v)
    (ρ : Representation k C (I → E))
    (hc : ∀ a d x, ρ a (fun i => σ d (x i)) = fun i => σ d (ρ a x i)) :
    ∃ μ : Representation F C (I → F),
      (∀ a c v, ρ a (fun i => c i • v) = fun i => μ a c i • v) ∧
      μ.asGroupHom.ker = ρ.asGroupHom.ker := by
  obtain ⟨μ,he⟩ := exists_multiplicity σ hs ρ hc
  refine ⟨μ,he,?_⟩
  ext a
  change μ.asGroupHom a = 1 ↔ ρ.asGroupHom a = 1
  constructor
  · intro ha
    apply Units.ext
    apply LinearMap.ext
    intro x
    have hexp : x = ∑ i : I, Pi.single i (x i) := by ext i; simp
    change ρ a x = x
    conv_lhs => rw [hexp,map_sum]
    conv_rhs => rw [hexp]
    apply Finset.sum_congr rfl
    intro i _
    have hsing (v : E) : (fun j => (Pi.single i (1 : F) : I → F) j • v) =
        Pi.single i v := by
      funext j
      by_cases h : i = j
      · subst j; simp
      · simp [Ne.symm h]
    have hh : μ a = 1 := congrArg Units.val ha
    rw [←hsing (x i),he,hh]
    rfl
  · intro ha
    obtain ⟨z,hz⟩ := exists_ne (0 : E)
    apply Units.ext
    apply LinearMap.ext
    intro c
    funext i
    apply smul_left_injective F hz
    have hh : ρ a = 1 := congrArg Units.val ha
    have hp := congrFun (he a c z) i
    rw [hh] at hp
    exact hp.symm
end Representation.ScalarMultiplicity
