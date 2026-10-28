module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalReduction
public import Theory.PGroupCore

/-!
# The two-core of the literal J₄ involution centralizer

Write C for `involutionCentralizer`, the intersection of `matrixGroup` with
the matrix centralizer of `matrixUnitA`, and Q for O₂(C). This module defines
Q and the actual conjugation homomorphism C → Aut(Q). The first generator is
a central involution of C and belongs to Q because it generates a normal
two-subgroup.

Two concrete local properties are left as explicit propositions: C_C(Q) is
contained in Q and has exponent two, and the image of C in Aut(Q) is
self-normalizing. The restriction argument in `LocalAction` uses these to
obtain inner squares. Neither property is asserted here.

Source motivation: GLS3, Table 5.3i, printed p.270,
`refs/KGroup/GLS3/Chapter5(sec3-).tex`, gives the 2A centralizer of J₄ the
shape `2^(1+12).(3M22.2)`. Identifying this structure in the literal matrices,
and any normalizer calculation used, remain proof obligations. In particular,
the separately constructed `max1Subgroup` is not substituted for C.
-/

@[expose] public section

namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares

/-- The characteristic two-core of the actual involution centralizer. -/
def involutionTwoCore : Subgroup involutionCentralizer := pCore 2 involutionCentralizer

instance involutionTwoCore_characteristic : involutionTwoCore.Characteristic :=
  inferInstanceAs (pCore 2 involutionCentralizer).Characteristic

/-- Conjugation on the actual two-core, with actors in the local group. -/
def involutionTwoCoreAction : involutionCentralizer →* MulAut involutionTwoCore :=
  MulAut.conjNormal

/-- The literal first matrix generator as an element of its centralizer. -/
def centralInvolution : involutionCentralizer :=
  ⟨matrixUnitA, matrixUnitA_mem_involutionCentralizer⟩

theorem centralInvolution_mem_center :
    centralInvolution ∈ Subgroup.center involutionCentralizer := by
  rw [Subgroup.mem_center_iff]
  intro x
  apply Subtype.ext
  exact ((mem_involutionCentralizer_iff _).mp x.property).2

theorem orderOf_centralInvolution : orderOf centralInvolution = 2 := by
  rw [← orderOf_injective involutionCentralizer.subtype Subtype.val_injective]
  change orderOf matrixUnitA = 2
  rw [← orderOf_injective (Units.coeHom BinaryMatrix) Units.val_injective]
  exact orderOf_matrixA

theorem centralInvolution_pow_two : centralInvolution ^ 2 = 1 := by
  simpa only [orderOf_centralInvolution] using pow_orderOf_eq_one centralInvolution

/-- A central involution generates a normal two-subgroup of C. -/
theorem centralInvolution_mem_twoCore : centralInvolution ∈ involutionTwoCore := by
  let Z := Subgroup.zpowers centralInvolution
  have hZ : Z ≤ Subgroup.center involutionCentralizer :=
    Subgroup.zpowers_le.mpr centralInvolution_mem_center
  have hn : Z.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [(Subgroup.mem_center_iff.mp (hZ hn)) g, mul_inv_cancel_right]
    exact hn
  have hp : IsPGroup 2 Z := IsPGroup.of_card (n := 1) (by
    rw [show Nat.card Z = orderOf centralInvolution from Nat.card_zpowers _,
      orderOf_centralInvolution, pow_one])
  have hle : Z ≤ involutionTwoCore :=
    le_sSup (show Z.Normal ∧ IsPGroup 2 Z from ⟨hn, hp⟩)
  exact hle (Subgroup.mem_zpowers centralInvolution)

/-- The kernel is a centralizer inside C, not in the ambient matrix group. -/
theorem involutionTwoCoreAction_ker :
    involutionTwoCoreAction.ker =
      Subgroup.centralizer (involutionTwoCore : Set involutionCentralizer) :=
  MulAut.conjNormal_ker_eq_centralizer involutionTwoCore

/-- Inner automorphisms of Q already come from actors in C. -/
theorem inner_le_involutionTwoCoreAction_range :
    (MulAut.conj (G := involutionTwoCore)).range ≤
      involutionTwoCoreAction.range := by
  rintro α ⟨q, rfl⟩
  exact ⟨q, MulAut.conjNormal_val⟩

/-- The precise centralizer input for the restriction-kernel calculation. -/
def LocalTwoCoreCentralizerControl : Prop :=
  Subgroup.centralizer (involutionTwoCore : Set involutionCentralizer) ≤ involutionTwoCore ∧
    ∀ z ∈ Subgroup.centralizer (involutionTwoCore : Set involutionCentralizer), z ^ 2 = 1

/-- The local conjugation image is self-normalizing in Aut(Q). This is a
separate local-structure obligation, not a conclusion of the source table. -/
def LocalTwoCoreActionSelfNormalizer : Prop :=
  Subgroup.normalizer (involutionTwoCoreAction.range : Set (MulAut involutionTwoCore)) ≤
    involutionTwoCoreAction.range

/-- The expected centralizer C_C(Q) = ⟨a⟩ would supply centralizer control. -/
theorem localTwoCoreCentralizerControl_of_eq_zpowers
    (h : Subgroup.centralizer (involutionTwoCore : Set involutionCentralizer) =
      Subgroup.zpowers centralInvolution) : LocalTwoCoreCentralizerControl := by
  constructor
  · rw [h]
    exact Subgroup.zpowers_le.mpr centralInvolution_mem_twoCore
  · intro z hz
    rw [h] at hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← zpow_natCast, ← zpow_mul, mul_comm k, zpow_mul, zpow_natCast,
      centralInvolution_pow_two, one_zpow]

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares
