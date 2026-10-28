module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.Source

/-!
# From quadratic four-groups to a quadratic axis group

For a fixed e, the actors centralizing the displacement space [V,e] form a
subgroup. Every quadratic four-group containing e lies in that subgroup.
Generation therefore makes the whole axis group centralize [V,e]. Applying
this to each e proves quadraticity, including the F₄ family of the source.

Source: Aschbacher–Smith B.4.9(1), printed p.92, combined manuscript of
1 March 2004. The matrix generation assertion remains a separate obligation.
-/

public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting
open QuasisimpleSource
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

private lemma conjugate_apply (g a : G) (v : V) :
    ρ (MulAut.conj g a) (ρ g v) = ρ g (ρ a v) := by
  change ρ (g * a * g⁻¹) (ρ g v) = _
  rw [← Module.End.mul_apply, ← map_mul]
  simp only [mul_assoc, inv_mul_cancel, mul_one, map_mul, Module.End.mul_apply]

/-- Quadraticity is preserved by conjugation in the original representation. -/
theorem quadratic_conjugate {E : Subgroup G} (hE : IsQuadratic ρ E) (g : G) :
    IsQuadratic ρ (E.map (MulAut.conj g).toMonoidHom) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ v
  change ρ (MulAut.conj g a) (ρ (MulAut.conj g b) v - v) =
    ρ (MulAut.conj g b) v - v
  have hv : ρ g (ρ g⁻¹ v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  conv_lhs => rw [← hv]
  conv_rhs => rw [← hv]
  rw [conjugate_apply, ← map_sub, conjugate_apply, hE a ha b hb, map_sub]

/-- A family of quadratic subgroups through each nonidentity element
propagates quadraticity to the subgroup it generates. -/
theorem quadratic_of_generation (Q : Subgroup G)
    (𝒜 : G → Set (Subgroup G))
    (hgen : ∀ e ∈ Q, e ≠ 1 → Q ≤ ⨆ (A : Subgroup G) (_ : A ∈ 𝒜 e), A)
    (hmem : ∀ e A, A ∈ 𝒜 e → e ∈ A)
    (hquad : ∀ e A, A ∈ 𝒜 e → IsQuadratic ρ A) : IsQuadratic ρ Q := by
  intro a ha e he v
  by_cases he1 : e = 1
  · subst e
    simp
  let C := subspaceKernel ρ (LinearMap.range (ρ e - LinearMap.id)) ⊤
  have hC : (⨆ (A : Subgroup G) (_ : A ∈ 𝒜 e), A) ≤ C := by
    refine iSup_le fun A => iSup_le fun hA => ?_
    intro b hb
    refine ⟨Subgroup.mem_top _, ?_⟩
    rintro _ ⟨w, rfl⟩
    exact hquad e A hA b hb e (hmem e A hA) w
  exact (hC (hgen e he he1 ha)).2 _ ⟨v, rfl⟩

variable {F : BinaryField} {n : ℕ} {ρ}

/-- Literal application to the four-subgroups of B.4.9(1). The only remaining
premise here is the stated axis-group generation, not quadraticity of Q. -/
theorem axis_quadratic (d : DoubleNatural F n ρ) (h : SourceHypotheses d)
    (E Q : Subgroup G) (hE : IsQuadratic ρ E) (hg : AxisGeneration d E Q) :
    IsQuadratic ρ Q := by
  apply quadratic_of_generation ρ Q (fun e => {A | e ∈ A ∧ AvailableFour d E A}) hg
  · exact fun _ _ hA => hA.1
  · intro _ A hA
    rcases hA.2 with ⟨g, rfl⟩ | ⟨hF, hfour, hroot⟩
    · exact quadratic_conjugate ρ hE g
    · exact h.fourField hF A hfour hroot

end CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting
