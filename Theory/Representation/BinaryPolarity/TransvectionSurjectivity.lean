module

public import Theory.Representation.BinaryPolarity.SymplecticAction
public import Theory.SpecificGroups.PSp4Three.Generation

/-!
# A marked full symplectic action from actual transvections

The original faithful action preserves its specified alternating form and
contains a transvection in every nonzero direction. Symplectic coordinates
retain that action on every original vector. The structural transvection
generation theorem makes the resulting matrix homomorphism surjective.
-/

public noncomputable section
namespace BinaryPolarity
open LinearMap Matrix Matrix.PSp4Three
variable {A V : Type*} [Group A] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]

/-- Actual transvections in every direction turn a marked faithful symplectic
action into a marked equivalence with the full standard symplectic group. -/
theorem exists_marked_symplectic_equiv_of_transvections
    (n : ℕ) (ρ : Representation (ZMod 2) A V) (hf : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) V = 2 * n)
    (B : LinearMap.BilinForm (ZMod 2) V) (hAlt : B.IsAlt) (hN : B.Nondegenerate)
    (hB : ∀ a x y, B (ρ a x) (ρ a y) = B x y)
    (ht : ∀ v : V, v ≠ 0 → ∃ a : A, ∀ x : V, ρ a x = x + (B x v) • v) :
    ∃ e : B.IsometryEquiv (Matrix.PSp4Three.form (n := n) (F := ZMod 2)),
      ∃ φ : A ≃* Matrix.PSp4Three.Sp n (ZMod 2),
        ∀ a x, (φ a).val *ᵥ (e x) = e (ρ a x) := by
  obtain ⟨e, φ, hφi, hφ⟩ := exists_marked_symplectic_action n ρ hf hd B hAlt hN hB
  have hφs : Function.Surjective φ := by
    apply MonoidHom.range_eq_top.mp
    apply top_unique
    rw [← transvectionGroup_eq_top (n := n) (F := ZMod 2)]
    unfold transvectionGroup
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨v, c, rfl⟩
    have hc : c = 0 ∨ c = 1 := (by decide +kernel : ∀ c : ZMod 2, c = 0 ∨ c = 1) c
    rcases hc with rfl | rfl
    · rw [Matrix.PSp4Three.transvection_zero]
      exact φ.range.one_mem
    by_cases hv : v = 0
    · rw [hv, transvection_zero_vector]
      exact φ.range.one_mem
    obtain ⟨a, ha⟩ := ht (e.symm v) (fun he => hv (by simpa using congrArg e he))
    refine ⟨a, ?_⟩
    apply ext_action
    intro w
    obtain ⟨x, rfl⟩ := e.surjective w
    change (φ a).val *ᵥ (e x) = Matrix.PSp4Three.transvection v 1 • (e x)
    rw [hφ, ha, map_add, map_smul,
      transvection_apply, one_mul]
    rw [← e.map_app (e.symm v) x]
    change e x + form (e x) (e (e.symm v)) • e (e.symm v) =
      e x + form (e x) v • v
    have hev : e (e.symm v) = v := e.toLinearEquiv.apply_symm_apply v
    rw [hev]
  exact ⟨e, MulEquiv.ofBijective φ ⟨hφi, hφs⟩, hφ⟩

end BinaryPolarity
