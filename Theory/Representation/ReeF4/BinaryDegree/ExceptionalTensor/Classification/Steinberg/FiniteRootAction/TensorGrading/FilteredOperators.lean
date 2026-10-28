module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.TensorGrading.CoordinateMaps

/-!
# Leading terms of filtered endomorphisms

Endomorphisms lowering a filtration by a prescribed integer form a submodule.
Composition adds the losses. When the loss is positive, the product of two
operators congruent to identity plus a leading term has leading term the sum;
the cross term loses at least one further layer. These elementary facts are
used on the actual tensor filtration, not as hypotheses on a new action.

Source: Steinberg (1963), Section 12, leading-term comparison.
-/

public section
noncomputable section
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction
universe u v
variable {F : Type u} [Field F] {V : Type v} [AddCommGroup V] [Module F V]

/-- Operators that lower every filtration layer by `d`. -/
@[expose] def loweringOperators (C : ℤ → Submodule F V) (d : ℤ) :
    Submodule F (Module.End F V) where
  carrier := {A | ∀ k v, v ∈ C k → A v ∈ C (k - d)}
  zero_mem' := by intro k v _; exact (C _).zero_mem
  add_mem' := by intro A D hA hD k v hv; exact (C _).add_mem (hA k v hv) (hD k v hv)
  smul_mem' := by intro c A hA k v hv; exact (C _).smul_mem c (hA k v hv)

theorem loweringOperators_antitone (C : ℤ → Submodule F V) (hC : Monotone C)
    {d e : ℤ} (h : d ≤ e) : loweringOperators C e ≤ loweringOperators C d := by
  intro A hA k v hv
  exact hC (by omega) (hA k v hv)

theorem loweringOperators_mul (C : ℤ → Submodule F V) {d e : ℤ}
    {A D : Module.End F V} (hA : A ∈ loweringOperators C d)
    (hD : D ∈ loweringOperators C e) : A * D ∈ loweringOperators C (d + e) := by
  intro k v hv
  have h := hA (k - e) (D v) (hD k v hv)
  simpa only [sub_sub, add_comm e d, Module.End.mul_apply] using h

/-- A filtered leading term, with an error at least one layer deeper. -/
@[expose] def HasLeadingTerm (C : ℤ → Submodule F V) (d : ℤ)
    (A L : Module.End F V) : Prop :=
  L ∈ loweringOperators C d ∧ A - 1 - L ∈ loweringOperators C (d + 1)

theorem HasLeadingTerm.sub_one {C : ℤ → Submodule F V} (hC : Monotone C)
    {d : ℤ} {A L : Module.End F V} (h : HasLeadingTerm C d A L) :
    A - 1 ∈ loweringOperators C d := by
  have he := loweringOperators_antitone C hC (show d ≤ d + 1 by omega) h.2
  simpa only [sub_add_cancel] using (loweringOperators C d).add_mem he h.1

theorem HasLeadingTerm.mul {C : ℤ → Submodule F V} (hC : Monotone C)
    {d : ℤ} (hd : 0 < d) {A D L M : Module.End F V}
    (hA : HasLeadingTerm C d A L) (hD : HasLeadingTerm C d D M) :
    HasLeadingTerm C d (A * D) (L + M) := by
  refine ⟨(loweringOperators C d).add_mem hA.1 hD.1, ?_⟩
  have hcross := loweringOperators_mul C (hA.sub_one hC) (hD.sub_one hC)
  have hcross' := loweringOperators_antitone C hC (show d + 1 ≤ d + d by omega) hcross
  have he := (loweringOperators C (d + 1)).add_mem
    ((loweringOperators C (d + 1)).add_mem hA.2 hD.2) hcross'
  convert he using 1
  noncomm_ring

/-- A root polynomial has its linear coefficient as leading term if all
coefficients have their actual integer weight loss. -/
theorem polynomial_hasLeadingTerm (C : ℤ → Submodule F V) (hC : Monotone C)
    (d : ℤ) (hd : 0 < d) (p : ℕ →₀ Module.End F V) (h0 : p 0 = 1)
    (hp : ∀ a : ℕ, p a ∈ loweringOperators C ((a : ℤ) * d)) (t : F) :
    HasLeadingTerm C d (p.sum fun a A => t ^ a • A) (t • p 1) := by
  classical
  refine ⟨(loweringOperators C d).smul_mem t (by simpa using hp 1), ?_⟩
  let q := p - Finsupp.single 0 (p 0) - Finsupp.single 1 (p 1)
  have hq (a : ℕ) (ha : a ∈ q.support) : 2 ≤ a := by
    have hn : q a ≠ 0 := Finsupp.mem_support_iff.mp ha
    by_contra h
    have : a = 0 ∨ a = 1 := by omega
    rcases this with rfl | rfl <;> simp [q] at hn
  have hmem : q.sum (fun a A => t ^ a • A) ∈ loweringOperators C (d + 1) := by
    apply Submodule.sum_mem
    intro a ha
    have ha2 := hq a ha
    have he := loweringOperators_antitone C hC (show d + 1 ≤ (a : ℤ) * d by
      have ha2' : (2 : ℤ) ≤ a := by exact_mod_cast ha2
      nlinarith) (hp a)
    have hqa : q a = p a := by simp [q, show a ≠ 0 by omega, show a ≠ 1 by omega]
    rw [hqa]
    exact (loweringOperators C (d + 1)).smul_mem _ he
  have heq : q.sum (fun a A => t ^ a • A) =
      p.sum (fun a A => t ^ a • A) - 1 - t • p 1 := by
    simp only [q, Finsupp.sum_sub_index (fun _ _ _ => smul_sub _ _ _), smul_zero,
      Finsupp.sum_single_index, pow_zero, one_smul, pow_one, h0]
  rwa [heq] at hmem

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction
