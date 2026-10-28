module

public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient
public import Theory.FieldTheory.BinaryTorusInvolution
public import Theory.FieldTheory.BinarySixDisplacement

/-!
# One-coordinate displacement witnesses in the degree-three tori

The field witness has parameters (σ(u)u⁻¹,1); the graph-field witness has
parameters (u⁻¹,σ(u)⁻¹). Projectivization kills precisely the cubic diagonal
scalars. It is injective on the first-coordinate subgroup, so the field
witness retains its full order. The graph witness is injective before
projectivization and its projective kernel has order at most three.

Over a field of order 64 these give lower bounds nine and twenty-one,
respectively. These are calculations in the actual Borel quotient parameter
groups of `BorelQuotient`; matrix-action compatibility is proved separately.
Source: Aschbacher–Smith, proof of 13.8.20, printed p.954.
-/

@[expose] public section

open Subgroup
open Matrix.PSL3.CartanActions.BorelQuotient
open FiniteField.BinaryTorusInvolution
namespace Matrix.PSL3.CartanActions.SixCommutators
variable (F : Type*) [Field F]

def firstCoordinate : Fˣ →* (Fˣ × Fˣ) where
  toFun u := (u, 1)
  map_one' := rfl
  map_mul' _ _ := by simp

def projectiveFirst : Fˣ →* ((Fˣ × Fˣ) ⧸ cubicScalars F) :=
  (QuotientGroup.mk' (cubicScalars F)).comp (firstCoordinate F)

theorem projectiveFirst_injective : Function.Injective (projectiveFirst F) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro u hu
  have h : firstCoordinate F u ∈ cubicScalars F := (QuotientGroup.eq_one_iff _).mp hu
  exact h.1

def fieldWitness (σ : F ≃+* F) : Fˣ →* (Fˣ × Fˣ) :=
  (firstCoordinate F).comp (displacement σ)

def graphWitness (σ : F ≃+* F) : Fˣ →* (Fˣ × Fˣ) where
  toFun u := (u⁻¹, (Units.map σ.toMonoidHom u)⁻¹)
  map_one' := by simp
  map_mul' _ _ := by simp [mul_comm]

def projectiveFieldWitness (σ : F ≃+* F) :
    Fˣ →* ((Fˣ × Fˣ) ⧸ cubicScalars F) :=
  (projectiveFirst F).comp (displacement σ)

def projectiveGraphWitness (σ : F ≃+* F) :
    Fˣ →* ((Fˣ × Fˣ) ⧸ cubicScalars F) :=
  (QuotientGroup.mk' (cubicScalars F)).comp (graphWitness F σ)

theorem graphWitness_injective (σ : F ≃+* F) : Function.Injective (graphWitness F σ) := by
  intro a b hab
  exact inv_injective (congrArg Prod.fst hab)

variable [Finite F]

theorem card_fieldWitness (σ : F ≃+* F) (hF : Nat.card F = 2 ^ 6)
    (hσ : ∀ x : F, σ x = x ^ 8) : Nat.card (fieldWitness F σ).range = 9 := by
  have hinj : Function.Injective (firstCoordinate F) := fun _ _ h => congrArg Prod.fst h
  rw [fieldWitness, MonoidHom.range_comp]
  rw [Nat.card_congr (equivMapOfInjective (displacement σ).range _ hinj).toEquiv.symm]
  exact card_displacement σ (m := 3) (by decide) hF hσ

theorem card_projectiveFieldWitness (σ : F ≃+* F) (hF : Nat.card F = 2 ^ 6)
    (hσ : ∀ x : F, σ x = x ^ 8) : Nat.card (projectiveFieldWitness F σ).range = 9 := by
  rw [projectiveFieldWitness, MonoidHom.range_comp]
  rw [Nat.card_congr (equivMapOfInjective (displacement σ).range _
    (projectiveFirst_injective F)).toEquiv.symm]
  exact card_displacement σ (m := 3) (by decide) hF hσ

omit [Finite F] in
theorem card_graphWitness (σ : F ≃+* F) (hF : Nat.card F = 2 ^ 6) :
    Nat.card (graphWitness F σ).range = 63 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (graphWitness_injective F σ)).toEquiv,
    Nat.card_units, hF]
  norm_num

theorem card_projectiveGraphWitness_ge (σ : F ≃+* F) (hF : Nat.card F = 2 ^ 6) :
    21 ≤ Nat.card (projectiveGraphWitness F σ).range := by
  let f := projectiveGraphWitness F σ
  have hker : f.ker ≤ (powMonoidHom 3 : Fˣ →* Fˣ).ker := by
    intro u hu
    have h : graphWitness F σ u ∈ cubicScalars F := (QuotientGroup.eq_one_iff _).mp hu
    have hh : (u⁻¹) ^ 3 = 1 := h.2
    simpa only [MonoidHom.mem_ker, powMonoidHom_apply, inv_pow, inv_eq_one] using hh
  have hker_card : Nat.card f.ker ≤ 3 := by
    have h := Subgroup.card_le_of_le hker
    have he : Nat.card (powMonoidHom 3 : Fˣ →* Fˣ).ker = 3 := by
      rw [IsCyclic.card_powMonoidHom_ker, Nat.card_units, hF]
      norm_num
    rwa [he] at h
  have hprod := f.ker.card_mul_index
  rw [index_ker, Nat.card_units, hF] at hprod
  change Nat.card f.ker * Nat.card f.range = 63 at hprod
  change 21 ≤ Nat.card f.range
  nlinarith

variable [CharP F 2]

/-- Every nontrivial field actor has a displacement image of order at least nine. -/
theorem card_fieldWitness_ge (σ : F ≃+* F) (hF : Nat.card F = 2 ^ 6)
    (hσ : σ ≠ 1) : 9 ≤ Nat.card (fieldWitness F σ).range := by
  have hinj : Function.Injective (firstCoordinate F) := fun _ _ h => congrArg Prod.fst h
  rw [fieldWitness, MonoidHom.range_comp]
  rw [Nat.card_congr (equivMapOfInjective (displacement σ).range _ hinj).toEquiv.symm]
  exact FiniteField.BinarySixDisplacement.card_displacement_ge σ hF hσ

/-- The scalar quotient does not reduce the one-coordinate field displacement. -/
theorem card_projectiveFieldWitness_ge (σ : F ≃+* F) (hF : Nat.card F = 2 ^ 6)
    (hσ : σ ≠ 1) : 9 ≤ Nat.card (projectiveFieldWitness F σ).range := by
  rw [projectiveFieldWitness, MonoidHom.range_comp]
  rw [Nat.card_congr (equivMapOfInjective (displacement σ).range _
    (projectiveFirst_injective F)).toEquiv.symm]
  exact FiniteField.BinarySixDisplacement.card_displacement_ge σ hF hσ

end Matrix.PSL3.CartanActions.SixCommutators
