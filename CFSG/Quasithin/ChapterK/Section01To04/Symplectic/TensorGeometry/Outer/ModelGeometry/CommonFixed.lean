module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Outer.ModelGeometry.SectionFaithfulness
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Outer.ModelGeometry.MaximalNatural

/-!
# Common fixed spaces in the Hermitian symplectic tensor

The quotient map on fixed vectors has kernel embedded in the displacement
invariants. Rank-nullity bounds the common fixed dimension by the sum of the
two section invariant dimensions. Faithfulness makes those dimensions at
most five and three for every nontrivial native subgroup.

When the subgroup order exceeds the base-field order, the actual diagonal
quotient equivalence and its injective Frobenius descent give at most two
middle invariants. Thus the common fixed dimension is strictly less than
eight at order `|k|³`, including `|k| = 2`. Restriction to the prime field
gives fixed dimension `10s` and common-fixed codimension at least `8s`,
strictly greater at maximal native rank. All quotients retain the literal
subspaces and scalar restrictions of the published model.

Source: Aschbacher–Smith, K.3.4.2, printed pp.456–457, following the
section method of H.4.4(6), printed p.381.
-/

@[expose] public section

open Representation
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Outer.Model.Geometry
noncomputable section

private lemma invariants_finrank_lt_of_faithful
    {k H W : Type*} [Field k] [Group H] [Nontrivial H]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (ρ : Representation k H W) (hρ : Function.Injective ρ) :
    Module.finrank k ρ.invariants < Module.finrank k W := by
  apply Submodule.finrank_lt
  intro htop
  obtain ⟨g, hg⟩ := exists_ne (1 : H)
  apply hg
  apply hρ
  ext w
  have hw : w ∈ ρ.invariants := htop ▸ Submodule.mem_top
  simpa using hw g

private lemma binary_field_finrank {k : Type*} [Field k] [Finite k]
    [Algebra (ZMod 2) k] {s : ℕ} (hcard : Nat.card k = 2 ^ s) : Module.finrank (ZMod 2) k = s := by
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := k)
  rw [Nat.card_zmod, hcard] at hc
  exact (Nat.pow_right_injective (by decide : 1 < 2) hc).symm


variable {k F : Type*} [Field k] [Field F] [Algebra k F]
  (σ : F ≃ₐ[k] F) (hσ : Function.Involutive σ)

local instance : AddCommGroup (Space σ hσ) := inferInstance
local instance : AddCommGroup (fieldFixed σ hσ) := inferInstance
local instance : AddCommGroup (fieldMoved σ hσ) := inferInstance

/-- The fixed vectors in the middle quotient receive the literal quotient map. -/
def commonToMiddle (B : Subgroup (Sp F)) (hB : B ≤ centralizer σ) :
    invariants ((fixedAction σ hσ).comp (Subgroup.inclusion hB)) →ₗ[k]
      invariants ((middleAction σ hσ).comp (Subgroup.inclusion hB)) :=
  ((movedInFixed σ hσ).mkQ.comp
    (invariants ((fixedAction σ hσ).comp (Subgroup.inclusion hB))).subtype).codRestrict _
    (by
      intro X b
      change middleAction σ hσ (Subgroup.inclusion hB b)
          ((movedInFixed σ hσ).mkQ X.val) = _
      rw [middleAction_mk]
      exact congrArg (movedInFixed σ hσ).mkQ (X.property b))

/-- Its kernel embeds into the actual displacement invariants. -/
def commonKernelToMoved (B : Subgroup (Sp F)) (hB : B ≤ centralizer σ) :
    LinearMap.ker (commonToMiddle σ hσ B hB) →ₗ[k]
      invariants ((movedAction σ hσ).comp (Subgroup.inclusion hB)) where
  toFun X := ⟨⟨X.val.val.val, by
    have hx := congrArg Subtype.val X.property
    change (movedInFixed σ hσ).mkQ X.val.val = 0 at hx
    exact (Submodule.Quotient.mk_eq_zero (movedInFixed σ hσ)).mp hx⟩, by
      intro b
      apply Subtype.ext
      change action σ hσ b.val X.val.val.val = X.val.val.val
      exact congrArg (fun Y : fieldFixed σ hσ => Y.val) (X.val.property b)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma commonKernelToMoved_injective (B : Subgroup (Sp F)) (hB : B ≤ centralizer σ) :
    Function.Injective (commonKernelToMoved σ hσ B hB) := by
  intro X Y h
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun Z => Z.val.val) h

/-- Invariants are left exact on the literal displacement/fixed/middle filtration. -/
lemma finrank_commonFixed_le_sections [FiniteDimensional k F]
    (B : Subgroup (Sp F)) (hB : B ≤ centralizer σ) :
    Module.finrank k (commonFixed σ hσ B) ≤
      Module.finrank k (invariants ((movedAction σ hσ).comp (Subgroup.inclusion hB))) +
      Module.finrank k (invariants ((middleAction σ hσ).comp (Subgroup.inclusion hB))) := by
  rw [finrank_commonFixed_eq σ hσ B hB]
  have hker := LinearMap.finrank_le_finrank_of_injective
    (commonKernelToMoved_injective σ hσ B hB)
  have hrange := Submodule.finrank_le (LinearMap.range (commonToMiddle σ hσ B hB))
  have hdim := (commonToMiddle σ hσ B hB).finrank_range_add_finrank_ker
  omega

variable [FiniteDimensional k F] [CharP k 2] [CharP F 2]
  (hdeg : Module.finrank k F = 2) (hne : σ ≠ AlgEquiv.refl)

include hdeg hne

omit [CharP k 2] in
lemma finrank_movedInvariants_le_five (B : Subgroup (Sp F))
    (hB : B ≤ centralizer σ) (hBne : B ≠ ⊥) :
    Module.finrank k (invariants ((movedAction σ hσ).comp (Subgroup.inclusion hB))) ≤ 5 := by
  let : Nontrivial B := (Subgroup.nontrivial_iff_ne_bot B).mpr hBne
  have hh := invariants_finrank_lt_of_faithful
    ((movedAction σ hσ).comp (Subgroup.inclusion hB))
    ((movedAction_faithful σ hσ hdeg hne).comp (Subgroup.inclusion_injective hB))
  rw [finrank_fieldMoved σ hσ hdeg hne] at hh
  omega

lemma finrank_middleInvariants_le_three (B : Subgroup (Sp F))
    (hB : B ≤ centralizer σ) (hBne : B ≠ ⊥) :
    Module.finrank k (invariants ((middleAction σ hσ).comp (Subgroup.inclusion hB))) ≤ 3 := by
  let : Nontrivial B := (Subgroup.nontrivial_iff_ne_bot B).mpr hBne
  have hh := invariants_finrank_lt_of_faithful
    ((middleAction σ hσ).comp (Subgroup.inclusion hB))
    ((middleAction_faithful σ hσ hdeg hne).comp (Subgroup.inclusion_injective hB))
  rw [finrank_middle σ hσ hdeg hne] at hh
  omega

/-- Every nontrivial native subgroup loses at least two dimensions on the fixed space. -/
theorem finrank_commonFixed_le_eight (B : Subgroup (Sp F))
    (hB : B ≤ centralizer σ) (hBne : B ≠ ⊥) :
    Module.finrank k (commonFixed σ hσ B) ≤ 8 := by
  have h := finrank_commonFixed_le_sections σ hσ B hB
  have hm := finrank_movedInvariants_le_five σ hσ hdeg hne B hB hBne
  have hq := finrank_middleInvariants_le_three σ hσ hdeg hne B hB hBne
  omega

/-- The middle section is at most a plane when the actor has order greater than the field. -/
theorem finrank_middleInvariants_le_two [Finite k] (B : Subgroup (Sp F))
    (hB : B ≤ centralizer σ) (hc : Nat.card k < Nat.card B) :
    Module.finrank k (invariants ((middleAction σ hσ).comp (Subgroup.inclusion hB))) ≤ 2 := by
  rw [finrank_middleInvariants_eq σ hσ hdeg hne B hB]
  let : Finite B := Finite.of_injective
    ((frobeniusDescent σ hdeg hne).comp (Subgroup.inclusion hB))
    ((frobeniusDescent_injective σ hdeg hne).comp (Subgroup.inclusion_injective hB))
  exact MaximalNatural.invariants_finrank_le_two_of_card_lt
    ((frobeniusDescent σ hdeg hne).comp (Subgroup.inclusion hB))
    ((frobeniusDescent_injective σ hdeg hne).comp (Subgroup.inclusion_injective hB)) hc

/-- The strict source estimate uses the actual Frobenius-natural middle section. -/
theorem finrank_commonFixed_lt_eight [Finite k] (B : Subgroup (Sp F))
    (hB : B ≤ centralizer σ) (hBne : B ≠ ⊥) (hc : Nat.card k < Nat.card B) :
    Module.finrank k (commonFixed σ hσ B) < 8 := by
  have h := finrank_commonFixed_le_sections σ hσ B hB
  have hm := finrank_movedInvariants_le_five σ hσ hdeg hne B hB hBne
  have hq := finrank_middleInvariants_le_two σ hσ hdeg hne B hB hc
  omega

/-- Maximal native rank gives strictness, with no exception for the two-element field. -/
theorem finrank_commonFixed_lt_eight_of_card_cube [Finite k] (B : Subgroup (Sp F))
    (hB : B ≤ centralizer σ) (hBne : B ≠ ⊥) (hc : Nat.card B = Nat.card k ^ 3) :
    Module.finrank k (commonFixed σ hσ B) < 8 := by
  apply finrank_commonFixed_lt_eight σ hσ hdeg hne B hB hBne
  rw [hc]
  simpa only [pow_one] using
    (Nat.pow_lt_pow_right (Finite.one_lt_card (α := k)) (by decide : 1 < 3))

/-- Codimension in the original Hermitian space, with its literal common-fixed quotient. -/
theorem finrank_commonFixed_quotient_ge_eight (B : Subgroup (Sp F))
    (hB : B ≤ centralizer σ) (hBne : B ≠ ⊥) :
    8 ≤ Module.finrank k ((Space σ hσ) ⧸ commonFixed σ hσ B) := by
  have hdim := (commonFixed σ hσ B).finrank_quotient_add_finrank
  rw [finrank_space σ hσ hdeg hne] at hdim
  have hfix := finrank_commonFixed_le_eight σ hσ hdeg hne B hB hBne
  omega

/-- Maximal native order gives strictly larger codimension, also over the binary base field. -/
theorem finrank_commonFixed_quotient_gt_eight_of_card_cube [Finite k]
    (B : Subgroup (Sp F)) (hB : B ≤ centralizer σ) (hBne : B ≠ ⊥)
    (hc : Nat.card B = Nat.card k ^ 3) :
    8 < Module.finrank k ((Space σ hσ) ⧸ commonFixed σ hσ B) := by
  have hdim := (commonFixed σ hσ B).finrank_quotient_add_finrank
  rw [finrank_space σ hσ hdeg hne] at hdim
  have hfix := finrank_commonFixed_lt_eight_of_card_cube σ hσ hdeg hne B hB hBne hc
  omega

section Binary
variable [Finite k] [Algebra (ZMod 2) k] [Algebra (ZMod 2) F]
  {s : ℕ} (hcard : Nat.card k = 2 ^ s)

include hcard

omit [CharP k 2] [CharP F 2] in
/-- The genuine model has the source binary dimension `16s`. -/
theorem finrank_space_binary : Module.finrank (ZMod 2) (Space σ hσ) = 16 * s := by
  rw [← Module.finrank_mul_finrank (ZMod 2) k (Space σ hσ),
    binary_field_finrank hcard, finrank_space σ hσ hdeg hne, Nat.mul_comm]

omit [CharP k 2] [CharP F 2] in
/-- The literal field-involution fixed space has the source binary dimension `10s`. -/
theorem finrank_fieldFixed_binary : Module.finrank (ZMod 2) (fieldFixed σ hσ) = 10 * s := by
  rw [← Module.finrank_mul_finrank (ZMod 2) k (fieldFixed σ hσ),
    binary_field_finrank hcard, finrank_fieldFixed σ hσ hdeg hne, Nat.mul_comm]

omit [CharP k 2] [CharP F 2] in
/-- The literal displacement space has binary dimension `6s`. -/
theorem finrank_fieldMoved_binary : Module.finrank (ZMod 2) (fieldMoved σ hσ) = 6 * s := by
  rw [← Module.finrank_mul_finrank (ZMod 2) k (fieldMoved σ hσ),
    binary_field_finrank hcard, finrank_fieldMoved σ hσ hdeg hne, Nat.mul_comm]

omit [CharP k 2] in
/-- The literal fixed/displacement quotient has binary dimension `4s`. -/
theorem finrank_middle_binary : Module.finrank (ZMod 2) (Middle σ hσ) = 4 * s := by
  rw [← Module.finrank_mul_finrank (ZMod 2) k (Middle σ hσ),
    binary_field_finrank hcard, finrank_middle σ hσ hdeg hne, Nat.mul_comm]

/-- Binary common-fixed dimension for every nontrivial native subgroup. -/
theorem finrank_commonFixed_binary_le (B : Subgroup (Sp F))
    (hB : B ≤ centralizer σ) (hBne : B ≠ ⊥) :
    Module.finrank (ZMod 2) (commonFixed σ hσ B) ≤ 8 * s := by
  rw [← Module.finrank_mul_finrank (ZMod 2) k (commonFixed σ hσ B), binary_field_finrank hcard]
  simpa only [Nat.mul_comm] using
    Nat.mul_le_mul_left s (finrank_commonFixed_le_eight σ hσ hdeg hne B hB hBne)

/-- Strict binary common-fixed dimension at maximal native rank, without excluding `s = 1`. -/
theorem finrank_commonFixed_binary_lt_of_card_cube (B : Subgroup (Sp F))
    (hB : B ≤ centralizer σ) (hBne : B ≠ ⊥) (hc : Nat.card B = Nat.card k ^ 3) :
    Module.finrank (ZMod 2) (commonFixed σ hσ B) < 8 * s := by
  have hs : 0 < s := by
    rw [← binary_field_finrank hcard]
    exact Module.finrank_pos
  rw [← Module.finrank_mul_finrank (ZMod 2) k (commonFixed σ hσ B), binary_field_finrank hcard]
  simpa only [Nat.mul_comm] using
    Nat.mul_lt_mul_of_pos_left
      (finrank_commonFixed_lt_eight_of_card_cube σ hσ hdeg hne B hB hBne hc) hs

/-- The source codimension bounds, in the original model over the prime field.
The quotient uses scalar restriction of the literal common-fixed subspace. -/
theorem commonFixed_binary_codimension_bounds (B : Subgroup (Sp F))
    (hB : B ≤ centralizer σ) (hBne : B ≠ ⊥) :
    8 * s ≤ Module.finrank (ZMod 2)
        ((Space σ hσ) ⧸ (commonFixed σ hσ B).restrictScalars (ZMod 2)) ∧
      (Nat.card B = Nat.card k ^ 3 → 8 * s < Module.finrank (ZMod 2)
        ((Space σ hσ) ⧸ (commonFixed σ hσ B).restrictScalars (ZMod 2))) := by
  let : FiniteDimensional (ZMod 2) (Space σ hσ) := Module.Finite.trans k (Space σ hσ)
  have hdim := ((commonFixed σ hσ B).restrictScalars (ZMod 2)).finrank_quotient_add_finrank
  rw [finrank_space_binary σ hσ hdeg hne hcard] at hdim
  have he : Module.finrank (ZMod 2) ((commonFixed σ hσ B).restrictScalars (ZMod 2)) =
      Module.finrank (ZMod 2) (commonFixed σ hσ B) :=
    ((Submodule.restrictScalarsEquiv (ZMod 2) k (Space σ hσ)
      (commonFixed σ hσ B)).restrictScalars (ZMod 2)).finrank_eq
  rw [he] at hdim
  constructor
  · have hfix := finrank_commonFixed_binary_le σ hσ hdeg hne hcard B hB hBne
    omega
  · intro hc
    have hfix := finrank_commonFixed_binary_lt_of_card_cube σ hσ hdeg hne hcard B hB hBne hc
    omega

end Binary

end
end CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Outer.Model.Geometry
