module

public import Theory.ElementaryAbelian.Extraspecial
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Cubic traces on an extraspecial projective basis

A rational representation in which every nonidentity central element acts as
minus identity has trace zero away from the center, provided its commutators
are central. Pairing with the inverse of a representative therefore proves
linear independence of the representatives of the central cosets. When their
number equals the dimension of the endomorphism space, they form a basis.

An automorphism of exponent dividing three, intertwined with a linear action
on that space, permutes these basis vectors up to sign. A fixed line cannot
have sign minus one. Its trace is consequently the number of fixed central
cosets. Neither algebraic closure nor irreducibility is needed.

The concrete application is the sixteen-dimensional octad complement in
`PolynomialSelection.TraceCount`: 256 central cosets form a basis of its
endomorphism space. This supplies the trace-to-count step in the setting of
Aschbacher, *Sporadic Groups* (1994), 25.1–25.5, 25.9 and §46. Exercise 9.6
is not used as a converse or as a class-selection theorem.
-/

public section

open scoped BigOperators commutatorElement
open Module
namespace Representation.ExtraspecialCubicTrace
variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℚ V]
  [FiniteDimensional ℚ V]

omit [FiniteDimensional ℚ V] in
/-- Central commutators acting by minus identity force noncentral trace zero. -/
theorem trace_zero_of_not_mem_center (ρ : G →* Module.End ℚ V)
    (hcomm : commutator G ≤ Subgroup.center G)
    (hcenter : ∀ z : Subgroup.center G, z.val ≠ 1 → ρ z.val = -1)
    {x : G} (hx : x ∉ Subgroup.center G) : LinearMap.trace ℚ V (ρ x) = 0 := by
  rw [Subgroup.mem_center_iff] at hx
  push Not at hx
  obtain ⟨y, hy⟩ := hx
  have hz : ⁅y, x⁆ ∈ Subgroup.center G := hcomm
    (Subgroup.commutator_mem_commutator (H₁ := ⊤) (H₂ := ⊤) (by trivial) (by trivial))
  have hzne : ⁅y, x⁆ ≠ 1 := fun h => hy (commutatorElement_eq_one_iff_mul_comm.mp h)
  have hs : ρ (y * x * y⁻¹) = -ρ x := by
    calc
      ρ (y * x * y⁻¹) = ρ (⁅y, x⁆ * x) := by simp [commutatorElement_def, mul_assoc]
      _ = -ρ x := by rw [map_mul, hcenter ⟨_, hz⟩ hzne]; simp
  have ht : LinearMap.trace ℚ V (ρ (y * x * y⁻¹)) = LinearMap.trace ℚ V (ρ x) := by
    simp only [ρ.map_mul]
    rw [mul_assoc, LinearMap.trace_mul_comm, mul_assoc,
      ← ρ.map_mul, inv_mul_cancel, map_one, mul_one]
  rw [hs, map_neg] at ht
  linarith

omit [FiniteDimensional ℚ V] in
/-- Representatives of the same central coset have images differing only by sign. -/
theorem same_coset_sign (ρ : G →* Module.End ℚ V)
    (hcenter : ∀ z : Subgroup.center G, z.val ≠ 1 → ρ z.val = -1)
    {x y : G} (hxy : (QuotientGroup.mk x : G ⧸ Subgroup.center G) = QuotientGroup.mk y) :
    ρ x = ρ y ∨ ρ x = -ρ y := by
  have hz := QuotientGroup.eq_iff_div_mem.mp hxy
  by_cases h : x / y = 1
  · exact Or.inl (congrArg ρ (div_eq_one.mp h))
  · right
    calc
      ρ x = ρ (x / y * y) := by rw [div_mul_cancel]
      _ = -ρ y := by rw [map_mul, hcenter ⟨_, hz⟩ h]; simp

/-- Trace pairing with inverse representatives separates all central cosets. -/
theorem projective_representatives_linearIndependent [Finite G] (ρ : G →* Module.End ℚ V)
    (hcomm : commutator G ≤ Subgroup.center G)
    (hcenter : ∀ z : Subgroup.center G, z.val ≠ 1 → ρ z.val = -1)
    (hdim : Module.finrank ℚ V ≠ 0) :
    LinearIndependent ℚ (fun q : G ⧸ Subgroup.center G => ρ q.out) := by
  classical
  let := Fintype.ofFinite (G ⧸ Subgroup.center G)
  apply Fintype.linearIndependent_iff.mpr
  intro c hc q
  let t : Module.End ℚ V →ₗ[ℚ] ℚ :=
    (LinearMap.trace ℚ V).comp (LinearMap.mulRight ℚ (ρ q.out⁻¹))
  have ht (s : G ⧸ Subgroup.center G) :
      t (ρ s.out) = if s = q then (Module.finrank ℚ V : ℚ) else 0 := by
    change LinearMap.trace ℚ V (ρ s.out * ρ q.out⁻¹) = _
    rw [← map_mul]
    split_ifs with h
    · subst s
      simp
    · apply trace_zero_of_not_mem_center ρ hcomm hcenter
      intro hz
      apply h
      have he : (QuotientGroup.mk s.out : G ⧸ Subgroup.center G) =
          QuotientGroup.mk q.out :=
        QuotientGroup.eq_iff_div_mem.mpr (by simpa only [div_eq_mul_inv] using hz)
      simpa using he
  have he := congrArg t hc
  simp only [map_sum, map_smul, map_zero, ht] at he
  have he' : c q * (Module.finrank ℚ V : ℚ) = 0 := by simpa using he
  exact (mul_eq_zero.mp he').resolve_right (by exact_mod_cast hdim)

/-- A signed basis action of exponent dividing three has one on each fixed diagonal entry. -/
theorem trace_signed_basis_of_cube {ι W : Type*} [Fintype ι] [AddCommGroup W] [Module ℚ W]
    (b : Basis ι ℚ W) (T : W →ₗ[ℚ] W) (a : ι → ι)
    (hT : ∀ i, T (b i) = b (a i) ∨ T (b i) = -b (a i))
    (hcube : ∀ i, T (T (T (b i))) = b i) :
    LinearMap.trace ℚ W T = (Nat.card {i // a i = i} : ℚ) := by
  classical
  have hd (i : ι) : b.repr (T (b i)) i = if a i = i then 1 else 0 := by
    by_cases hi : a i = i
    · have hf : T (b i) = b i := by
        rcases hT i with h | h
        · simpa [hi] using h
        · rw [hi] at h
          have hh := hcube i
          simp only [h, map_neg, neg_neg] at hh
          have hz := congrArg (fun w => b.repr w i) hh
          norm_num at hz
      simp [hf, hi]
    · rcases hT i with h | h <;> simp [h, hi, Ne.symm hi]
  rw [LinearMap.trace_eq_matrix_trace ℚ b]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply]
  simp only [hd]
  simp [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- The endomorphism trace counts fixed central cosets for a compatible cubic action. -/
theorem trace_eq_card_fixed [Finite G] (ρ : G →* Module.End ℚ V)
    (hcomm : commutator G ≤ Subgroup.center G)
    (hcenter : ∀ z : Subgroup.center G, z.val ≠ 1 → ρ z.val = -1)
    (hdim : Module.finrank ℚ V ≠ 0)
    (hcard : Nat.card (G ⧸ Subgroup.center G) = Module.finrank ℚ (Module.End ℚ V))
    (α : MulAut G) (a : (G ⧸ Subgroup.center G) → (G ⧸ Subgroup.center G))
    (ha : ∀ x : G, a (QuotientGroup.mk x) = QuotientGroup.mk (α x))
    (hα : α ^ 3 = 1) (T : Module.End ℚ (Module.End ℚ V))
    (hT : ∀ x, T (ρ x) = ρ (α x)) :
    LinearMap.trace ℚ (Module.End ℚ V) T =
      (Nat.card {q : G ⧸ Subgroup.center G // a q = q} : ℚ) := by
  classical
  let := Fintype.ofFinite (G ⧸ Subgroup.center G)
  let b : Basis (G ⧸ Subgroup.center G) ℚ (Module.End ℚ V) :=
    basisOfLinearIndependentOfCardEqFinrank
      (projective_representatives_linearIndependent ρ hcomm hcenter hdim)
      (by simpa only [Nat.card_eq_fintype_card] using hcard)
  have hb (q : G ⧸ Subgroup.center G) : b q = ρ q.out := by
    simp [b]
  apply trace_signed_basis_of_cube b T a
  · intro q
    simp only [hb, hT]
    apply same_coset_sign ρ hcenter
    calc
      QuotientGroup.mk (α q.out) = a (QuotientGroup.mk q.out) := (ha _).symm
      _ = a q := by simp
      _ = QuotientGroup.mk (a q).out := by simp
  · intro q
    simp only [hb, hT]
    have h := DFunLike.congr_fun hα q.out
    change α (α (α q.out)) = q.out at h
    rw [h]

end Representation.ExtraspecialCubicTrace
