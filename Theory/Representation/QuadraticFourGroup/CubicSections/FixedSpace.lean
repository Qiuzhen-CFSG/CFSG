module

public import Theory.Representation.QuadraticFourGroup.CubicSections.Descent

/-!
# Cubic fixed spaces on actual subquotients

In characteristic two, the norm `v + xv + x²v` lifts every fixed vector of a
cubic element through an equivariant surjection. Thus fixed-space containment
passes to arbitrary invariant subquotients. If the fixed vectors in the
original module are group invariants, every nontrivial irreducible section
is fixed-point free for that cubic element.

These are the section-transfer steps used in GLS, volume 2, Theorem 25.14,
Steps 2–4. Only subspaces invariant under the group acting on the section are
used; no ambient four-group action on an arbitrary section is presumed.
-/

@[expose] public section

namespace Representation.QuadraticFourGroup

variable {G V W : Type*} [Group G]
  [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) G V} {σ : Representation (ZMod 2) G W}

private theorem binary_add_self (v : W) : v + v = 0 := by
  have h := @two_smul (ZMod 2) W _ _ _ v
  have htwo : (2 : ZMod 2) = 0 := by decide
  rw [htwo, zero_smul] at h
  exact h.symm

/-- Cubic fixed vectors lift along every equivariant surjection in
characteristic two, by averaging the three elements of the cyclic group. -/
theorem exists_cubic_fixed_lift (f : ρ.IntertwiningMap σ)
    (hf : Function.Surjective f) {x : G} (hx : x ^ 3 = 1)
    {w : W} (hw : σ x w = w) : ∃ v : V, ρ x v = v ∧ f v = w := by
  obtain ⟨v, rfl⟩ := hf w
  refine ⟨ρ x (ρ x v) + ρ x v + v, ?_, ?_⟩
  · have hxv : ρ x (ρ x (ρ x v)) = v := by
      calc _ = ρ (x ^ 3) v := by simp [pow_succ, map_mul, Module.End.mul_apply]
           _ = v := by rw [hx, map_one]; rfl
    simp only [map_add, hxv]
    abel
  · simp only [map_add, f.isIntertwining, hw, binary_add_self, zero_add]

/-- A fixed-space containment for a cubic element descends to a quotient. -/
theorem cubic_fixed_imp_of_surjective (f : ρ.IntertwiningMap σ)
    (hf : Function.Surjective f) {x y : G} (hx : x ^ 3 = 1)
    (h : ∀ v, ρ x v = v → ρ y v = v) :
    ∀ w, σ x w = w → σ y w = w := by
  intro w hw
  obtain ⟨v, hv, rfl⟩ := exists_cubic_fixed_lift f hf hx hw
  rw [← f.isIntertwining, h v hv]

/-- Fixed-space containment by a cubic element survives actual invariant
subquotients; the invariant spaces need not be stable under any other group. -/
theorem cubic_fixed_imp_irreducibleSection {x y : G} (hx : x ^ 3 = 1)
    (h : ∀ v, ρ x v = v → ρ y v = v) (hs : IsIrreducibleSection ρ σ) :
    ∀ w, σ x w = w → σ y w = w := by
  obtain ⟨_, U, N, ⟨e⟩⟩ := hs
  have hU (v : U) (hv : U.toRepresentation x v = v) :
      U.toRepresentation y v = v :=
    Subtype.ext (h v (congrArg Subtype.val hv))
  let q : U.toRepresentation.IntertwiningMap N.quotientRepresentation :=
    ⟨N.toSubmodule.mkQ, fun _ => rfl⟩
  have hN := cubic_fixed_imp_of_surjective q N.toSubmodule.mkQ_surjective hx hU
  exact cubic_fixed_imp_of_surjective e.toIntertwiningMap
    e.toLinearEquiv.surjective hx hN

/-- A nontrivial irreducible module has no nonzero invariant vector. -/
theorem eq_zero_of_fixed_of_nontrivial_irreducible [σ.IsIrreducible]
    (hn : ¬ σ.IsTrivial) (w : W) (hw : ∀ g, σ g w = w) : w = 0 := by
  by_contra hw0
  have ht : (⊤ : Subgroup G) ≤ σ.ker :=
    le_ker_of_normal_invariants_ne_bot σ ⊤ (by
      intro hb
      have hw' : w ∈ invariants (σ.comp (⊤ : Subgroup G).subtype) := fun g => hw g
      rw [hb] at hw'
      exact hw0 hw')
  apply hn
  exact ⟨fun g => ht (by trivial : g ∈ (⊤ : Subgroup G))⟩

/-- If the only vectors fixed by a cubic element are group invariants,
that element is fixed-point free on every nontrivial irreducible section.
Trivial sections are retained and excluded only by the explicit `hn`. -/
theorem cubic_fixed_free_irreducibleSection {x : G} (hx : x ^ 3 = 1)
    (h : ∀ v, ρ x v = v → ∀ g, ρ g v = v)
    (hs : IsIrreducibleSection ρ σ) (hn : ¬ σ.IsTrivial) :
    ∀ w, σ x w = w → w = 0 := by
  let := hs.1
  intro w hw
  exact eq_zero_of_fixed_of_nontrivial_irreducible hn w (fun g =>
    cubic_fixed_imp_irreducibleSection hx (fun v hv => h v hv g) hs w hw)

end Representation.QuadraticFourGroup

end
