module
public import Theory.Representation.Suzuki.ExchangedTensor
public import Theory.Representation.BinaryOffender.SchurNormalizerDisplacement

/-!
# Suzuki tensor exchange bounds without a Schur-linearity hypothesis

A faithful irreducible binary representation of a Suzuki square has at least
 twice the minimum degree of either factor: Clifford restriction is semisimple,
 and the commuting perfect factor rules out an irreducible restriction. Thus
 its degree is at least `8*(2*r+1)`.

An involution exchanging the factors either commutes with the actual Schur
 field, when the tensor calculation moves at least three-eighths of the space,
 or moves the field, when the Schur displacement estimate moves at least half.
 Both cases give displacement at least `3*(2*r+1)` without a coefficient-field
 hypothesis. The original Chapter 10 seed application uses its literal marked
 product quotient and its actual conjugation operator.

Source: Aschbacher--Smith D.3.7, printed pp.197--198; the Schur-field alternative
 is the standard semilinear displacement argument.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MonoidAlgebra
namespace Representation.Suzuki
open BenderSuzuki.MatrixGroups
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

theorem binary_square_finrank_ge (r : ℕ) (hr : 0 < r)
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup r × SuzukiMatrixGroup r) V)
    (hi : ρ.IsIrreducible) (hf : Function.Injective ρ) :
    8 * (2*r+1) ≤ Module.finrank (ZMod 2) V := by
  let S := SuzukiMatrixGroup r
  let J : Subgroup (S × S) := (⊤ : Subgroup S).prod ⊥
  let K : Subgroup (S × S) := (⊥ : Subgroup S).prod ⊤
  let eJ : J ≃* S := {
    toFun x := x.val.1
    invFun x := ⟨(x,1),mem_top x,rfl⟩
    left_inv x := Subtype.ext (Prod.ext rfl (mem_bot.mp x.property.2).symm)
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  let eK : K ≃* S := {
    toFun x := x.val.2
    invFun x := ⟨(1,x),rfl,mem_top x⟩
    left_inv x := Subtype.ext (Prod.ext (mem_bot.mp x.property.1).symm rfl)
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  let : Fact (0 < r) := ⟨hr⟩
  let : IsSimpleGroup J := eJ.isSimpleGroup
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := eK.symm.toMonoidHom) eK.symm.surjective
  let : Nontrivial K := eK.surjective.nontrivial
  let := hi
  let := Subrepresentation.irreducible_module_nontrivial ρ
  have hJn : J ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot J).mp inferInstance
  have hfix := fixedSpace_eq_bot_of_normal_faithful_irreducible ρ hf hi J hJn
  let := NormalConstituentDisplacement.restriction_semisimple ρ hi J
  have hc : K ≤ centralizer (J : Set (S × S)) := by
    intro k hk j hj
    apply Prod.ext
    · simp only [Prod.fst_mul,mem_bot.mp hk.1,mul_one,one_mul]
    · simp only [Prod.snd_mul,mem_bot.mp hj.2,mul_one,one_mul]
  have hb := two_mul_le_finrank_of_commuting_perfect ρ hf J K hc (4*(2*r+1)) (by
    intro U hU
    exact finrank_ge (by omega : 1 ≤ r) (U.toRepresentation.comp eJ.symm.toMonoidHom)
      ((simple_subrepresentation_faithful_of_fixed_eq_bot (ρ.comp J.subtype) hfix U hU).comp
        eJ.symm.injective))
  omega

theorem binary_product_exchange_displacement_unconditional
    {J : Type*} [Group J]
    (r : ℕ) (hr : 0 < r) (e : J ≃* SuzukiMatrixGroup r)
    (ρ : Representation (ZMod 2) (J × J) V) (hi : ρ.IsIrreducible)
    (hf : Function.Injective ρ)
    (T : Module.End (ZMod 2) V) (h2 : T*T=1)
    (hT : ∀ g v, T (ρ g v) = ρ (g.2,g.1) (T v)) :
    3 * Module.finrank (ZMod 2) V ≤ 8 * Module.finrank (ZMod 2) (T-1).range := by
  let u : (Module.End (ZMod 2) V)ˣ := ⟨T,T,h2,h2⟩
  have hu2 : u*u=1 := Units.ext h2
  have huinv : u⁻¹=u := inv_eq_of_mul_eq_one_left hu2
  have hconj (g : J × J) : u * ρ.asGroupHom g * u⁻¹ = ρ.asGroupHom (g.2,g.1) := by
    apply Units.ext
    apply LinearMap.ext
    intro v
    change T (ρ g (T v)) = ρ (g.2,g.1) v
    rw [hT]
    have hh := LinearMap.congr_fun h2 v
    exact congrArg (ρ (g.2,g.1)) hh
  have hu : u ∈ linearNormalizer ρ := by
    apply mem_normalizer_iff.mpr
    intro x
    constructor
    · rintro ⟨g,rfl⟩
      exact ⟨(g.2,g.1),(hconj g).symm⟩
    · rintro ⟨g,hg⟩
      have hh := congrArg (fun z => u*z*u⁻¹) hg
      rw [hconj] at hh
      have hround : u*(u*x*u⁻¹)*u⁻¹=x := by
        rw [huinv]
        calc
          u*(u*x*u)*u = (u*u)*x*(u*u) := by group
          _ = x := by rw [hu2,one_mul,mul_one]
      rw [hround] at hh
      exact ⟨(g.2,g.1),hh⟩
  let a : linearNormalizer ρ := ⟨u,hu⟩
  by_cases hs : SchurNormalizer.IsSchurLinear ρ a
  · exact binary_product_exchange_displacement r hr e ρ hi hf T h2 hT hs
  · let := hi
    have hb := SchurNormalizer.finrank_le_twice_fixedCodim ρ a hs
    rw [fixedCodim_zpowers_eq_displacement_rank] at hb
    change Module.finrank (ZMod 2) V ≤ 2 * Module.finrank (ZMod 2) (T-1).range at hb
    omega

theorem binary_square_exchange_displacement_ge (r : ℕ) (hr : 0 < r)
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup r × SuzukiMatrixGroup r) V)
    (hi : ρ.IsIrreducible) (hf : Function.Injective ρ)
    (T : Module.End (ZMod 2) V) (h2 : T*T=1)
    (hT : ∀ g v, T (ρ g v) = ρ (g.2,g.1) (T v)) :
    3 * (2*r+1) ≤ Module.finrank (ZMod 2) (T-1).range := by
  have hd := binary_square_finrank_ge r hr ρ hi hf
  have hb := binary_product_exchange_displacement_unconditional r hr (MulEquiv.refl _) ρ hi hf T h2 hT
  omega
end Representation.Suzuki
