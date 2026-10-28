module

public import Theory.SpecificGroups.Monster.Construction.LocalC.SourceNormalizer.Orientation.QuarterTurnGeneration.Construction
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.QuadraticQuotient

/-!
# The action of quarter turns on the central square form

Every automorphism of `Q1Image` fixes the central involution and induces a
binary linear isometry of the actual central quotient. The square and
commutator identities identify the quarter turn at `q` with the nonsingular
symmetry `v ↦ v + B(qZ,v) • qZ`. All quotient maps use the actual center.

Source: Aschbacher, *Sporadic Groups*, Exercise 4.4 and Exercise 4.6, p. 64;
the square-form coordinates in Section 27, pp. 144–145.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

open scoped commutatorElement IsMulCommutative
open Atlas.Codes
noncomputable section
namespace Sporadic.Monster.Construction.LocalC.SourceNormalizer
open TrialitySpin

abbrev CentralSpace := Additive Q1CentralQuotient

def centralVector (x : Q1Image) : CentralSpace :=
  Additive.ofMul (QuotientGroup.mk' (Subgroup.center Q1Image) x)

theorem centralVector_surjective : Function.Surjective centralVector :=
  QuotientGroup.mk'_surjective _

@[simp] theorem centralVector_mul (x y : Q1Image) :
    centralVector (x*y) = centralVector x + centralVector y :=
  map_mul (QuotientGroup.mk' _) x y

private theorem generator_pow_bit_injective :
    Function.Injective (fun b : Bit => q1ImageCenterGenerator ^ b.val) := by
  intro a b h
  fin_cases a <;> fin_cases b <;>
    simp_all [ZMod.val_one_eq_one_mod, q1ImageCenterGenerator_ne_one,Ne.symm q1ImageCenterGenerator_ne_one]

@[simp] theorem centralVector_square_iff (x : Q1Image) :
    q1CentralQuadraticForm (centralVector x) = 1 ↔ x^2 = q1ImageCenterGenerator := by
  change q1CentralQuadraticForm (Additive.ofMul (QuotientGroup.mk' _ x)) = 1 ↔ _
  rw [q1CentralQuadraticForm_square]
  exact ⟨fun h => by rw [h]; simp [ZMod.val_one_eq_one_mod],
    fun h => generator_pow_bit_injective (h.trans (by simp [ZMod.val_one_eq_one_mod]))⟩

def centralAutomorphism (α : MulAut Q1Image) : CentralSpace ≃ₗ[Bit] CentralSpace :=
  { MulEquiv.toAdditive (QuotientGroup.congr _ _ α
      (Subgroup.characteristic_iff_map_eq.mp inferInstance α)) with
    map_smul' := ZMod.map_smul _ }

@[simp] theorem centralAutomorphism_vector (α : MulAut Q1Image) (x : Q1Image) :
    centralAutomorphism α (centralVector x) = centralVector (α x) := rfl

theorem centralAutomorphism_preserves (α : MulAut Q1Image) (v : CentralSpace) :
    q1CentralQuadraticForm (centralAutomorphism α v) = q1CentralQuadraticForm v := by
  obtain ⟨x,rfl⟩ := centralVector_surjective v
  apply generator_pow_bit_injective
  change q1ImageCenterGenerator ^ (q1CentralQuadraticForm (centralVector (α x))).val =
    q1ImageCenterGenerator ^ (q1CentralQuadraticForm (centralVector x)).val
  unfold centralVector
  rw [← q1CentralQuadraticForm_square,
    ← map_pow, q1CentralQuadraticForm_square, map_pow,
    automorphism_fixes_center α _ (by
      rw [Q1Image_center]; exact Subgroup.mem_zpowers _)]

theorem commutator_polar (x y : Q1Image) :
    ⁅x,y⁆ = q1ImageCenterGenerator ^
      (q1CentralQuadraticForm.polarBilin (centralVector x) (centralVector y)).val := by
  rw [q1CentralQuadraticForm_polar]
  exact Q1Image_commutator_coordinates x y

theorem commute_iff_polar_zero (x y : Q1Image) :
    Commute x y ↔ q1CentralQuadraticForm.polarBilin (centralVector x) (centralVector y) = 0 := by
  rw [← commutatorElement_eq_one_iff_commute,commutator_polar]
  constructor
  · intro h
    exact generator_pow_bit_injective (h.trans (by simp))
  · intro h
    rw [h]
    simp

theorem quarterTurn_centralVector (q : Q1Image) (hq : q^2 = q1ImageCenterGenerator)
    (x : Q1Image) :
    centralVector (quarterTurn q hq x) = centralVector x +
      q1CentralQuadraticForm.polarBilin (centralVector q) (centralVector x) • centralVector q := by
  have hspec := quarterTurn_spec q hq
  by_cases h : Commute q x
  · rw [(hspec x).1 h,(commute_iff_polar_zero q x).mp h,zero_smul,add_zero]
  · have hp : q1CentralQuadraticForm.polarBilin (centralVector q) (centralVector x) = 1 := by
      have hn := mt (commute_iff_polar_zero q x).mpr h
      generalize q1CentralQuadraticForm.polarBilin (centralVector q) (centralVector x) = b at *
      fin_cases b
      · exact (hn rfl).elim
      · rfl
    rw [(hspec x).2 h,centralVector_mul,hp,one_smul,add_comm]

end Sporadic.Monster.Construction.LocalC.SourceNormalizer
