module

public import Theory.Representation.BinaryOffender.SmallRank
public import Theory.Representation.BinaryOffender.QuadraticSection
public import Theory.Representation.DualCommutator

/-!
# Rank-three actors on a representation and its dual

Displacement embeds a faithful actor into Hom(U/C_U(A), [U,A]). Duality
identifies the dimension of [U,A] with the fixed codimension on U*. Thus
rank(A) ≤ r*s, where r and s are the two fixed codimensions. If r+s ≤ 3,
then r*s ≤ 2. No quadratic-action hypothesis is needed.

The concrete application is the induced eight-space in the HS paragraph of
Guralnick--Malle, Classification of 2F-modules I, Proposition 5.1, pp.16--17.
Its separate model comparison must identify the outer-conjugate summand
with the actual dual before applying this intrinsic inequality.
-/

public section
namespace Representation.BinaryOffender

variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U]

/-- Rank at least three forces total fixed codimension at least four on a
faithful representation paired with its dual. -/
theorem four_le_fixedCodim_prod_dual_of_rank_three
    (ρ : Representation (ZMod 2) H U) (hρ : Function.Injective ρ)
    (A : Subgroup H) (hrank : 3 ≤ rank A) :
    4 ≤ fixedCodim (ρ.prod ρ.dual) A := by
  let C := Coinvariants.ker (ρ.comp A.subtype)
  have hc : fixedCodim ρ.dual A = Module.finrank (ZMod 2) C :=
    finrank_quotient_dual_invariants_eq_commutator (ρ.comp A.subtype)
  have hr := rank_le_fixed_codim_mul_displacement_dim ρ hρ A (fixedSpace ρ A) C le_rfl
    (fun a ha v => Coinvariants.sub_mem_ker (ρ := ρ.comp A.subtype) ⟨a, ha⟩ v)
  change rank A ≤ fixedCodim ρ A * Module.finrank (ZMod 2) C at hr
  rw [← hc] at hr
  rw [fixedCodim_prod]
  by_contra hn
  have hx : fixedCodim ρ A ≤ 3 := by omega
  have hy : fixedCodim ρ.dual A ≤ 3 := by omega
  interval_cases h₁ : fixedCodim ρ A <;>
    interval_cases h₂ : fixedCodim ρ.dual A <;> omega

end Representation.BinaryOffender
