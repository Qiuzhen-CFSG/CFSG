module

public import Theory.Character.InductionTransitivity
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# One-dimensional and abelian monomial characters

The trace of a one-dimensional representation is multiplicative, since every
operator is scalar. Inducing that homomorphism from the whole group gives the
same character. Schur's lemma consequently makes every irreducible character
of a finite abelian group monomial.

Source: Serre, *Linear Representations of Finite Groups*, the treatment of
one-dimensional representations and induced characters.
-/

public section
noncomputable section
open scoped BigOperators
attribute [local instance] Fintype.ofFinite

namespace Theory.Character
/-- A one-dimensional character is a multiplicative complex-valued function. -/
theorem exists_monoidHom_character_of_finrank_one
    {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
    (hdim : Module.finrank ℂ V = 1) :
    ∃ linear : G →* ℂ, ρ.character = linear := by
  refine ⟨{ toFun := ρ.character, map_one' := ?_, map_mul' := ?_ }, rfl⟩
  · simp [Representation.character, hdim]
  · intro g h
    obtain ⟨a, ha, _⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim (ρ g)
    obtain ⟨b, hb, _⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim (ρ h)
    simp [Representation.character, map_mul, ha, hb, hdim, mul_comm,
      ← Module.End.one_eq_id]

/-- A linear character is induced from the top subgroup. -/
theorem monomial_of_monoidHom {G : Type*} [Group G] [Fintype G]
    (linear : G →* ℂ) :
    ∃ (K : Subgroup G) (μ : K →* ℂ), (linear : ClassFunction G) =
      inducedClassFunction K μ := by
  refine ⟨⊤, linear.comp (⊤ : Subgroup G).subtype, ?_⟩
  funext g
  have hval (x : G) : linear (x⁻¹ * g * x) = linear g := by
    rw [map_mul, map_mul, mul_comm (linear x⁻¹), mul_assoc, ← map_mul,
      inv_mul_cancel, map_one, mul_one]
  simp only [inducedClassFunction, Subgroup.mem_top, ↓reduceDIte,
    MonoidHom.comp_apply, Subgroup.subtype_apply, hval, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  have hcard : Fintype.card {x : G // True} = Fintype.card G :=
    Fintype.card_congr ⟨Subtype.val, fun x => ⟨x, trivial⟩, fun _ => rfl, fun _ => rfl⟩
  rw [hcard]
  exact (inv_mul_cancel_left₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) _).symm

/-- Every one-dimensional complex representation has a monomial character. -/
theorem monomial_of_finrank_one {G : Type*} [Group G] [Fintype G]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (hdim : Module.finrank ℂ V = 1) :
    ∃ (K : Subgroup G) (linear : K →* ℂ), ρ.character = inducedClassFunction K linear := by
  obtain ⟨linear, hlinear⟩ := exists_monoidHom_character_of_finrank_one ρ hdim
  rw [hlinear]
  exact monomial_of_monoidHom linear

/-- Irreducible characters of finite abelian groups are monomial. -/
theorem irreducible_monomial_of_isMulCommutative
    {G : Type*} [Group G] [Fintype G] [IsMulCommutative G]
    {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ) :
    ∃ (K : Subgroup G) (linear : K →* ℂ), χ = inducedClassFunction K linear := by
  obtain ⟨n, ρ, hρ, rfl⟩ := hχ
  let := hρ
  exact monomial_of_finrank_one ρ
    (Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative ρ)


end Theory.Character
