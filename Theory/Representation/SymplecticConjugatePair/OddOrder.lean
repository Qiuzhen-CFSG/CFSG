module

public import Theory.Representation.SymplecticConjugatePair
public import Theory.Representation.SymplecticConjugatePair.OddOrder.Linear
public import Theory.Representation.SymplecticConjugatePair.OddOrder.Residual
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.TwoLocalCover.FixedRadical

/-!
# Odd-order displacement on a paired symplectic module

The fixed space of a nonidentity odd-order symplectic matrix is a proper
nondegenerate alternating space, hence has dimension zero or two in the
natural four-space. This applies to both the matrix and its image under
any twisting automorphism. Their paired fixed space is the literal product;
restriction of scalars gives the binary bound 4n over a field of order 2ⁿ.

Source: Aschbacher–Smith H.7, printed p.389, combined manuscript of
1 March 2004. These theorems concern matrix actors. Reduction of an actor
in a larger group to this case, and the binary strengthening to six,
remain separate obligations.
-/

@[expose] public section

namespace SymplecticConjugatePair.OddOrder
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.TwoLocalCover (form_alternating form_nondegenerate)
open Representation Representation.BinaryOffender Module
open scoped Matrix
variable {F : Type*} [Field F]

/-- The actual fixed subspace on the natural four-space over the coefficient field. -/
noncomputable def naturalFixed (g : Sp F) : Submodule F (Vector F) :=
  invariants ((symplecticNatural 2).comp (Subgroup.zpowers g).subtype)

/-- Fixation by the cyclic group is fixation by its generator. -/
theorem mem_naturalFixed (g : Sp F) (v : Vector F) :
    v ∈ naturalFixed g ↔ symplecticNatural 2 g v = v := by
  apply Representation.mem_invariants_iff_of_forall_mem_zpowers
    ((symplecticNatural 2).comp (Subgroup.zpowers g).subtype) ⟨g, Subgroup.mem_zpowers g⟩
  intro x
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp x.property
  exact Subgroup.mem_zpowers_iff.mpr ⟨n, Subtype.ext hn⟩

/-- Faithfulness of the matrix action excludes a full fixed space. -/
theorem naturalFixed_ne_top {g : Sp F} (hg : g ≠ 1) : naturalFixed g ≠ ⊤ := by
  intro ht
  apply hg
  apply Subtype.ext
  ext i j
  have hv := congrFun ((mem_naturalFixed g (Pi.single j 1)).mp
    (ht ▸ Submodule.mem_top)) i
  change (g.val *ᵥ Pi.single j 1) i = _ at hv
  simpa [Matrix.mulVec_single, Pi.single_apply, Matrix.one_apply] using hv

variable [Finite F] [CharP F 2]

/-- Odd-order fixed spaces are nondegenerate symplectic subspaces. -/
theorem even_finrank_naturalFixed (g : Sp F) (ho : Odd (orderOf g)) :
    Even (finrank F (naturalFixed g)) := by
  let : Fintype (Subgroup.zpowers g) := Fintype.ofFinite _
  have hc : (Fintype.card (Subgroup.zpowers g) : F) = 1 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_zpowers]
    exact natCast_eq_one_of_odd_of_two_eq_zero ho (CharP.cast_eq_zero F 2)
  let : Invertible (Fintype.card (Subgroup.zpowers g) : F) :=
    invertibleOfNonzero (by rw [hc]; exact one_ne_zero)
  exact even_finrank_of_nondegenerate ((form F).restrict (naturalFixed g))
    (fun v => form_alternating.self_eq_zero v.val)
    (invariants_nondegenerate ((symplecticNatural 2).comp (Subgroup.zpowers g).subtype)
      (form F) form_alternating form_nondegenerate (fun g x y => preserves_form g.val x y))

/-- A nonidentity odd-order actor moves two or four coefficient-field dimensions. -/
theorem natural_codim_cases {g : Sp F} (hg : g ≠ 1) (ho : Odd (orderOf g)) :
    finrank F (Vector F ⧸ naturalFixed g) = 2 ∨
      finrank F (Vector F ⧸ naturalFixed g) = 4 := by
  have hn : finrank F (naturalFixed g) < 4 := by
    simpa [Theory.SpecificGroups.SymplecticFour.Vector] using Submodule.finrank_lt (naturalFixed_ne_top hg)
  obtain ⟨k, hk⟩ := even_finrank_naturalFixed g ho
  have hsum := (naturalFixed g).finrank_quotient_add_finrank
  have hd : finrank F (Vector F) = 4 := by simp [Theory.SpecificGroups.SymplecticFour.Vector]
  omega

variable [Algebra (ZMod 2) F]

omit [Finite F] [CharP F 2] in
/-- The paired fixed space is the actual product of the two natural fixed spaces. -/
theorem binaryPair_fixedSpace (τ : MulAut (Sp F)) (g : Sp F) :
    fixedSpace (binaryPair τ) (Subgroup.zpowers g) =
      ((naturalFixed g).prod (naturalFixed (τ g))).restrictScalars (ZMod 2) := by
  ext v
  rw [mem_fixedSpace_zpowers_iff]
  change (symplecticNatural 2 g v.1, symplecticNatural 2 (τ g) v.2) = v ↔
    v.1 ∈ naturalFixed g ∧ v.2 ∈ naturalFixed (τ g)
  rw [Prod.ext_iff, mem_naturalFixed, mem_naturalFixed]

omit [CharP F 2] in
/-- Restriction of scalars multiplies the sum of the two codimensions by the field degree. -/
theorem binaryPair_fixedCodim (τ : MulAut (Sp F)) (g : Sp F) :
    fixedCodim (binaryPair τ) (Subgroup.zpowers g) = finrank (ZMod 2) F *
      (finrank F (Vector F ⧸ naturalFixed g) +
       finrank F (Vector F ⧸ naturalFixed (τ g))) := by
  have hc := fixedCodim_add_finrank (binaryPair τ) (Subgroup.zpowers g)
  rw [binaryPair_fixedSpace] at hc
  have hf : finrank (ZMod 2)
      (((naturalFixed g).prod (naturalFixed (τ g))).restrictScalars (ZMod 2)) =
      finrank (ZMod 2) F * (finrank F (naturalFixed g) + finrank F (naturalFixed (τ g))) := by
    rw [(((naturalFixed g).prod (naturalFixed (τ g))).restrictScalarsEquiv
      (ZMod 2)).restrictScalars (ZMod 2) |>.finrank_eq]
    rw [← Module.finrank_mul_finrank (ZMod 2) F]
    let e : ((naturalFixed g).prod (naturalFixed (τ g))) ≃ₗ[F]
        (naturalFixed g) × (naturalFixed (τ g)) := {
      toFun v := (⟨v.val.1, v.property.1⟩, ⟨v.val.2, v.property.2⟩)
      invFun v := ⟨(v.1.val, v.2.val), v.1.property, v.2.property⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
    rw [e.finrank_eq, Module.finrank_prod]
  have hdim : finrank (ZMod 2) (Space F) = finrank (ZMod 2) F * 8 := by
    rw [← Module.finrank_mul_finrank (ZMod 2) F]
    simp [Space, Theory.SpecificGroups.SymplecticFour.Vector, Module.finrank_prod]
  have h1 := (naturalFixed g).finrank_quotient_add_finrank
  have h2 := (naturalFixed (τ g)).finrank_quotient_add_finrank
  have hd : finrank F (Vector F) = 4 := by simp [Theory.SpecificGroups.SymplecticFour.Vector]
  rw [hf, hdim] at hc
  nlinarith

/-- Every nonidentity odd-order matrix actor has paired binary codimension at least 4n. -/
theorem four_mul_le_fixedCodim (τ : MulAut (Sp F)) {g : Sp F}
    (hg : g ≠ 1) (ho : Odd (orderOf g)) {n : ℕ} (hF : Nat.card F = 2^n) :
    4*n ≤ fixedCodim (binaryPair τ) (Subgroup.zpowers g) := by
  have ht : τ g ≠ 1 := fun h => hg (τ.injective (h.trans τ.map_one.symm))
  have hto : Odd (orderOf (τ g)) := by rwa [τ.orderOf_eq]
  have h1 := natural_codim_cases hg ho
  have h2 := natural_codim_cases ht hto
  rw [binaryPair_fixedCodim, coefficient_finrank hF]
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2] <;> omega
end SymplecticConjugatePair.OddOrder

namespace SymplecticConjugatePair.OddOrder
open Theory.SpecificGroups.SymplecticFour
open Module Representation.BinaryOffender
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

/-- On either actual summand the binary codimension is 2n or 4n. -/
theorem binary_natural_codim_cases {g : Sp F} (hg : g ≠ 1) (ho : Odd (orderOf g))
    {n : ℕ} (hF : Nat.card F = 2^n) :
    finrank (ZMod 2) (Vector F ⧸ (naturalFixed g).restrictScalars (ZMod 2)) = 2*n ∨
      finrank (ZMod 2) (Vector F ⧸ (naturalFixed g).restrictScalars (ZMod 2)) = 4*n := by
  rw [(Submodule.Quotient.restrictScalarsEquiv (ZMod 2) (naturalFixed g)).finrank_eq]
  rw [← Module.finrank_mul_finrank (ZMod 2) F, coefficient_finrank hF]
  rcases natural_codim_cases hg ho with h | h <;> simp [h, Nat.mul_comm]
end SymplecticConjugatePair.OddOrder
