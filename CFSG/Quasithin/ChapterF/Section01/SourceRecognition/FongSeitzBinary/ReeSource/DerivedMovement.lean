module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.BinaryDerivedMovement
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.BinaryDerivedRadical
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.MixedBounds

/-!
# Faithful derived radical sections from the two natural panel markings

The linear panel makes its actual root elementary, and source (6.3)
centralizes the shifted Suzuki root by the actual Omega root. The binary
movement theorem therefore applies to the corrected source reflection and
central involution, without an assumed movement witness. Together with the
positive-parameter argument this proves faithful derived Frattini action and
the q⁴ lower bound for every Suzuki parameter. Local characteristic two
then bounds Φ([V,V]) by the two independent field orders.

Source: Fong--Seitz I (1973), the effective-module step preceding (6.1),
printed p.52. Pairing, odd linear degree, the positive-parameter centralizer
estimates, the nonzero mixed commutators and later coordinates are not
asserted here. OriginalDerivedMovement gives the same original-endpoint
and literal Q.q applications, including genuine movement on the quotient.
-/

@[expose] public noncomputable section
open Subgroup
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
variable {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
  {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) (i j : Fin 2)
  (ν : (Endpoint Q j ⧸ panelKernel Q j) ≃* PSL(2,F))
  (T : Sylow 2 PSL(2,F))
  (hC : (quotientBorel Q j).map ν.toMonoidHom = normalizer (T : Set PSL(2,F)))

include ν hC in
private theorem marked_linear_elementary : IsElementaryAbelian 2 (simpleRoot Q split j) := by
  let : IsElementaryAbelian 2 (Multiplicative F) := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := by
      apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      intro x
      change 2 • x.toAdd = 0
      exact (two_nsmul _).trans (CharTwo.add_self_eq_zero _)
  }
  exact IsElementaryAbelian.of_injective (linearRootEquiv Q split j ν T hC).toMonoidHom
    (linearRootEquiv Q split j ν T hC).injective

variable (μ₀ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup 0)
  (hB₀ : (quotientBorel Q i).map μ₀.toMonoidHom =
    normalizer (SuzukiRootSubgroup 0 : Set (SuzukiMatrixGroup 0)))

include ν hC μ₀ hB₀ in
/-- Both the order and genuine derived-section movement of the source binary mover. -/
theorem source_binary_derived_movement (hm : rotationOrder Q = 8) (hij : i ≠ j) :
    orderOf (frattiniMover Q split i 0 μ₀ hB₀) = 5 ∧
      (derivedRadicalSection Q split i
        (marked_suzuki_remainder_le_kernel Q split i 0 μ₀ hB₀)).action
          (frattiniMover Q split i 0 μ₀ hB₀) ≠ 1 := by
  have hcomm := (source_six_three Q split i j 0 μ₀ hB₀ ν T hC hm hij).2
  exact ⟨binary_frattiniMover_order Q split i
      (marked_suzuki_remainder_le_kernel Q split i 0 μ₀ hB₀) μ₀ hB₀ hm j hij hcomm,
    binary_frattiniMover_moves_derived Q split i j μ₀ hB₀
      (marked_suzuki_remainder_le_kernel Q split i 0 μ₀ hB₀) hm hij
      (marked_linear_elementary Q split j ν T hC) hcomm⟩

variable (m : ℕ) (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))

include ν hC μ hB in
/-- The actual derived Frattini action is faithful for every Suzuki parameter. -/
theorem source_derivedRadical_effective (hm : rotationOrder Q = 8) (hij : i ≠ j) :
    Function.Injective (derivedRadicalSection Q split i
      (marked_suzuki_remainder_le_kernel Q split i m μ hB)).effectiveAction := by
  by_cases hm0 : m = 0
  · subst m
    exact binary_derivedRadical_effectiveAction_injective_of_octagon Q split i j μ hB
      (marked_suzuki_remainder_le_kernel Q split i 0 μ hB) hm hij
      (marked_linear_elementary Q split j ν T hC)
      (source_six_three Q split i j 0 μ hB ν T hC hm hij).2
  · exact derivedRadical_effectiveAction_injective Q split i
      (marked_suzuki_remainder_le_kernel Q split i m μ hB) m μ hB hm (by omega)

include ν hC μ hB in
/-- The q⁴ derived Frattini lower bound, including Sz(2), with no movement callback. -/
theorem source_derivedRadical_frattini_card_ge (hm : rotationOrder Q = 8) (hij : i ≠ j) :
    (2^(2*m+1))^4 ≤ Nat.card
      ((⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D)) ⧸
        frattini (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D))) := by
  by_cases hm0 : m = 0
  · subst m
    obtain ⟨ho,hmove⟩ := source_binary_derived_movement Q split i j ν T hC μ hB hm hij
    exact binary_derivedRadical_frattini_card_ge Q split i
      (marked_suzuki_remainder_le_kernel Q split i 0 μ hB) μ hB _ ho hmove
  · exact derivedRadical_frattini_card_ge Q split i
      (marked_suzuki_remainder_le_kernel Q split i m μ hB) m μ hB hm (by omega)

include ν hC μ hB in
/-- Both effective layers bound Φ([V,V]), with independent field orders and all m ≥ 0. -/
theorem source_derived_frattini_weighted_card_le
    (hc : centralizer (pCore 2 (Endpoint Q i) : Set (Endpoint Q i)) ≤ pCore 2 (Endpoint Q i))
    (hm : rotationOrder Q = 8) (hij : i ≠ j) :
    Nat.card (frattini (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ :
      Subgroup (X ⧸ Q.D))) * (2^(2*m+1))^2 ≤ Nat.card F^4 := by
  let V := simpleRemainder Q split i
  let D : Subgroup (X ⧸ Q.D) := ⁅V,V⁆
  let q := 2^(2*m+1)
  let : Fact (IsPGroup 2 V) := ⟨split.isTwo.to_le inf_le_left⟩
  have hDc : Nat.card D = Nat.card (commutator V) := by
    rw [show D = (commutator V).map V.subtype from (map_subtype_commutator V).symm,
      card_map_of_injective V.subtype_injective]
  have hD : Nat.card D ≤ q^2*Nat.card (simpleRoot Q split j)^4 := by
    rw [hDc]
    exact (Nat.le_of_dvd Nat.card_pos
      (card_dvd_of_le (commutator_le_frattini_of_isPGroup (p := 2)))).trans
      (suzuki_radical_frattini_card_le Q split i j m μ hB
        (marked_suzuki_remainder_le_kernel Q split i m μ hB) hc hm hij)
  have hquot : q^4 ≤ Nat.card (D ⧸ frattini D) :=
    source_derivedRadical_frattini_card_ge Q split i j ν T hC m μ hB hm hij
  have he := (frattini D).card_mul_index
  change Nat.card (frattini D) * Nat.card (D ⧸ frattini D) = Nat.card D at he
  have hh : (Nat.card (frattini D)*q^2)*q^2 ≤ Nat.card (simpleRoot Q split j)^4*q^2 := by
    calc
      _ = Nat.card (frattini D)*q^4 := by ring
      _ ≤ Nat.card (frattini D)*Nat.card (D ⧸ frattini D) := Nat.mul_le_mul_left _ hquot
      _ = Nat.card D := he
      _ ≤ q^2*Nat.card (simpleRoot Q split j)^4 := hD
      _ = _ := Nat.mul_comm _ _
  have hle := Nat.le_of_mul_le_mul_right hh (by dsimp [q]; positivity)
  rw [Nat.card_congr (linearRootEquiv Q split j ν T hC).toEquiv,
    Nat.card_congr Multiplicative.ofAdd.symm] at hle
  exact hle

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
