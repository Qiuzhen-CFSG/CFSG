module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.ActualAction
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# The concrete four-element scalar field of cubic conjugation

The polynomial X²+X+1 is irreducible over F₂, and its root field has four
elements. Evaluation at the actual cubic conjugation operator factors
through that field because β²+β+1=0. Restricting the natural endomorphism
module along this ring map gives the actual F₄ structure on U, with its
root acting as b-conjugation and its F₂ scalars unchanged. The same
polynomial identity proves that cubic conjugation is fixed-point-free.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
the semilinear module argument following 15.3.68, printed pp.1154–1155.
-/

@[expose] public section
open Subgroup Representation Polynomial
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear

/-- The irreducible polynomial satisfied by the actual cubic operator. -/
noncomputable def cubicPolynomial : (ZMod 2)[X] := X ^ 2 + X + 1

private theorem cubicPolynomial_degree : cubicPolynomial.natDegree = 2 := by
  unfold cubicPolynomial
  compute_degree
  decide

theorem cubicPolynomial_irreducible : Irreducible cubicPolynomial := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [cubicPolynomial_degree]
    decide
  · intro x
    simp only [Polynomial.IsRoot,cubicPolynomial,eval_add,eval_pow,eval_X,eval_one]
    fin_cases x <;> decide

instance cubicPolynomial_irreducible_fact : Fact (Irreducible cubicPolynomial) :=
  ⟨cubicPolynomial_irreducible⟩

/-- The concrete field F₂[α]/(α²+α+1). -/
abbrev CubicField := AdjoinRoot cubicPolynomial

theorem cubicField_card : Nat.card CubicField = 4 := by
  have hp : cubicPolynomial ≠ 0 := cubicPolynomial_irreducible.ne_zero
  let b := (AdjoinRoot.powerBasis hp).basis
  have he := Nat.card_congr b.equivFun.toEquiv
  change Nat.card CubicField = Nat.card (Fin cubicPolynomial.natDegree → ZMod 2) at he
  rw [cubicPolynomial_degree] at he
  simpa using he

variable {X₀ : Type*} [AddCommGroup X₀] [Module (ZMod 2) X₀]

/-- Evaluate field scalars at the actual cubic endomorphism. -/
noncomputable def cubicScalarHom (β : Module.End (ZMod 2) X₀)
    (hβ : β ^ 2 + β + 1 = 0) : CubicField →+* Module.End (ZMod 2) X₀ :=
  Ideal.Quotient.lift _ (aeval β).toRingHom (by
    intro p hp
    obtain ⟨r,hr⟩ := Ideal.mem_span_singleton.mp hp
    rw [hr,map_mul]
    have he : aeval β cubicPolynomial = 0 := by
      simpa only [cubicPolynomial,map_add,map_pow,aeval_X,map_one] using hβ
    change (aeval β) cubicPolynomial * (aeval β) r = 0
    rw [he,zero_mul])

/-- The field generator acts by the chosen cubic operator. -/
theorem cubicScalarHom_root (β : Module.End (ZMod 2) X₀)
    (hβ : β ^ 2 + β + 1 = 0) :
    cubicScalarHom β hβ (AdjoinRoot.root cubicPolynomial) = β := by
  exact aeval_X β

/-- The polynomial identity gives an actual F₄-module structure in every dimension. -/
@[instance_reducible] noncomputable def cubicFieldModule (β : Module.End (ZMod 2) X₀)
    (hβ : β ^ 2 + β + 1 = 0) : Module CubicField X₀ :=
  Module.compHom X₀ (cubicScalarHom β hβ)

theorem cubicFieldModule_root_smul (β : Module.End (ZMod 2) X₀)
    (hβ : β ^ 2 + β + 1 = 0) :
    letI := cubicFieldModule β hβ
    ∀ x : X₀, (AdjoinRoot.root cubicPolynomial) • x = β x := by
  intro x
  exact LinearMap.congr_fun (cubicScalarHom_root β hβ) x

/-- The field action restricts to the original binary scalar action. -/
theorem cubicFieldModule_base_smul (β : Module.End (ZMod 2) X₀)
    (hβ : β ^ 2 + β + 1 = 0) :
    letI := cubicFieldModule β hβ
    ∀ (a : ZMod 2) (x : X₀), (algebraMap (ZMod 2) CubicField a) • x = a • x := by
  intro a x
  exact LinearMap.congr_fun (aeval_C β a) x

variable {G : Type*} [Group G] [Finite G]

/-- The actual cubic conjugation makes U a vector space over the concrete
four-element field. -/
@[instance_reducible] noncomputable def externalCubicFieldModule
    (B U : Subgroup G) [IsElementaryAbelian 2 U]
    (hBU : B ≤ normalizer (U : Set G))
    (h0U : ambientTwoCore B ≤ centralizer (U : Set G))
    (hc : Nat.card (B ⧸ localTwoCore B) = 3) (hgen : U = ⁅U,B⁆)
    (b : B) (hb : b ∉ localTwoCore B) : Module CubicField (Additive U) :=
  cubicFieldModule (externalCubicAction B U hBU h0U (QuotientGroup.mk' _ b))
    (externalCubicAction_polynomial B U hBU h0U hc hgen b hb)

/-- The field generator is literal conjugation by the chosen cubic lift. -/
theorem externalCubicFieldModule_root_smul
    (B U : Subgroup G) [IsElementaryAbelian 2 U]
    (hBU : B ≤ normalizer (U : Set G))
    (h0U : ambientTwoCore B ≤ centralizer (U : Set G))
    (hc : Nat.card (B ⧸ localTwoCore B) = 3) (hgen : U = ⁅U,B⁆)
    (b : B) (hb : b ∉ localTwoCore B) :
    letI := externalCubicFieldModule B U hBU h0U hc hgen b hb
    ∀ u : Additive U, (((AdjoinRoot.root cubicPolynomial) • u).toMul : G) =
      (b : G) * (u.toMul : G) * (b : G)⁻¹ := by
  intro u
  exact congrArg (fun v : Additive U => (v.toMul : G))
    (cubicFieldModule_root_smul
      (externalCubicAction B U hBU h0U (QuotientGroup.mk' _ b))
      (externalCubicAction_polynomial B U hBU h0U hc hgen b hb) u)

/-- Cubic conjugation has no nonzero fixed vector on the actual U. -/
theorem externalCubicAction_fixed_free
    (B U : Subgroup G) [IsElementaryAbelian 2 U]
    (hBU : B ≤ normalizer (U : Set G))
    (h0U : ambientTwoCore B ≤ centralizer (U : Set G))
    (hc : Nat.card (B ⧸ localTwoCore B) = 3) (hgen : U = ⁅U,B⁆)
    (b : B) (hb : b ∉ localTwoCore B) (u : Additive U)
    (hu : externalCubicAction B U hBU h0U (QuotientGroup.mk' _ b) u = u) : u = 0 := by
  have hp := LinearMap.congr_fun (externalCubicAction_polynomial B U hBU h0U hc hgen b hb) u
  change externalCubicAction B U hBU h0U (QuotientGroup.mk' _ b)
    (externalCubicAction B U hBU h0U (QuotientGroup.mk' _ b) u) +
      externalCubicAction B U hBU h0U (QuotientGroup.mk' _ b) u + u = 0 at hp
  rw [hu,hu] at hp
  have htwo : u + u = 0 := by
    simpa only [show (1 : ZMod 2) + 1 = 0 by decide,zero_smul,one_smul] using
      (add_smul (1 : ZMod 2) 1 u).symm
  simpa only [htwo,zero_add] using hp

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear
