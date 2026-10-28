module

public import Theory.Representation.PrimeFixedPointCentralization.Reduction.Image
public import Theory.Representation.ExtraspecialFixedPoints
public import Mathlib.RepresentationTheory.Maschke

/-!
# A constituent detecting a moved element

Maschke's theorem ensures that some irreducible constituent detects each
nontrivial element of a faithful odd-order binary representation. Apply this
to a commutator between the actor and the q-group, and pass to the faithful
image of that constituent. A fixed vector in the constituent is a fixed vector
in the original module.

Source: Aschbacher, *Finite Group Theory*, second edition, the irreducibility
reduction in the proof of 36.2, printed p.194.
-/

universe u
namespace Representation.PrimeFixedPointCentralization

/-- Remove irreducibility while retaining minimality of the group action. -/
public theorem fixed_vector_of_minimal_action
    {q r : ℕ} [Fact q.Prime] [Fact r.Prime]
    (hqodd : Odd q) (hrodd : Odd r) (hqr : q ≠ r)
    (hfixed : MinimalFixedVectorStatement.{u} q r)
    {P A W : Type u} [Group P] [Finite P] [Group A] [Finite A]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (hP : IsPGroup q P) (hA : Nat.card A = r)
    (φ : A →* MulAut P) (hφ : Function.Injective φ) (hmin : IsMinimalAction φ)
    (ρ : Representation (ZMod 2) (SemidirectProduct P A φ) W)
    (hfaith : Function.Injective ρ) :
    ∃ v : W, v ≠ 0 ∧ ∀ a : A, ρ (SemidirectProduct.inr a) v = v := by
  classical
  let S := SemidirectProduct P A φ
  let : Finite S := Finite.of_equiv (P × A) SemidirectProduct.equivProd.symm
  have hodd : Odd (Nat.card S) := by
    obtain ⟨n, hn⟩ := hP.exists_card_eq
    rw [SemidirectProduct.card, hn, hA]
    exact hqodd.pow.mul hrodd
  let : NeZero (Nat.card S : ZMod 2) := ⟨by
    rw [ne_eq, CharP.cast_eq_zero_iff (ZMod 2) 2]
    exact hodd.not_two_dvd_nat⟩
  have hmoving : ∃ a z, φ a z ≠ z := by
    by_contra! h
    let : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp
      (hA ▸ (Fact.out : r.Prime).one_lt)
    obtain ⟨a, ha⟩ := exists_ne (1 : A)
    apply ha
    apply hφ
    ext z
    simpa using h a z
  obtain ⟨a, z, haz⟩ := hmoving
  let x : S := SemidirectProduct.inl (φ a z)
  let y : S := SemidirectProduct.inl z
  let d : S := x * y⁻¹
  have hd : d ≠ 1 := by
    intro heq
    have heq' : x = y := mul_inv_eq_one.mp heq
    exact haz (SemidirectProduct.inl_injective heq')
  have hnotker : ¬ Subgroup.zpowers d ≤ ρ.ker := by
    intro h
    have heq : ρ d = 1 := h (Subgroup.mem_zpowers d)
    exact hd (hfaith (by simpa using heq))
  obtain ⟨m, hm, hdetect⟩ :=
    exists_simple_submodule_nontrivial_of_not_le_ker ρ (Subgroup.zpowers d) hnotker
  let M := Subrepresentation.ofSubmodule' m
  let σ := M.toRepresentation
  have hirr : IsIrreducible σ := irreducible_of_ofSubmodule'_simple ρ hm
  let : FiniteDimensional (ZMod 2) M.toSubmodule :=
    finiteDimensional_of_irreducible_finite_group σ hirr
  have hσmoving : ∃ a z, σ (SemidirectProduct.inl (φ a z)) ≠
      σ (SemidirectProduct.inl z) := by
    refine ⟨a, z, ?_⟩
    intro heq
    apply hdetect
    apply Subgroup.zpowers_le.mpr
    change σ d = 1
    change σ (x * y⁻¹) = 1
    rw [map_mul, show σ x = σ y from heq, ← map_mul, mul_inv_cancel, map_one]
  obtain ⟨v, hv, hvA⟩ := fixed_vector_of_irreducible_moving hqr hfixed hP hA
    φ hmin σ hirr hσmoving
  refine ⟨(v : W), ?_, fun b => ?_⟩
  · intro hv0
    exact hv (Subtype.ext hv0)
  · exact congrArg Subtype.val (hvA b)

end Representation.PrimeFixedPointCentralization
