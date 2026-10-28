module

public import Theory.SpecificGroups.SL3.InvolutionConjugacy
public import Theory.SpecificGroups.SL3.InvolutionDerived
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison
public import Theory.GroupAction.PerfectCentralQuotient.FixedResidual
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2


/-!
# The perfect block and involutions in PSL₃(7)

The determinant-corrected GL₂ embedding restricts to an SL₂(7) block in
SL₃(7). The last diagonal entry is one, so this block meets the scalar center
trivially and remains an actual SL₂(7) after projectivization. It is perfect
and fixed by the standard inner involution.

The center of SL₃(7) has order three. Cubing a lift of a projective involution
therefore produces an involution with the same image. The existing linear
involution-conjugacy theorem then gives the projective conjugacy statement.
No assertion about arbitrary automorphisms or their pointwise fixers is made.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, A.3.21(a),
printed p.55, and the PSL₃(7) case in the proof of 15.3.38, printed p.1137.
The scalar-center count is reused from the attributed ATLAS import in
`Theory.SpecificGroups.PSL3.ProjectionKernel`.
-/

@[expose] public section

open scoped MatrixGroups
open Subgroup

namespace Matrix.PSL3.SevenAction

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- The specified projective matrix group, with its actual scalar quotient. -/
abbrev Model := PSL(3, ZMod 7)

/-- The determinant-one two-dimensional block in SL₃(7). -/
def blockSL : SL(2, ZMod 7) →* SL(3, ZMod 7) :=
  (SL3.blockEmbedding (ZMod 7)).comp SpecialLinearGroup.toGL

/-- The block followed by the canonical central quotient projection. -/
def blockMap : SL(2, ZMod 7) →* Model :=
  (PSL3.projection (ZMod 7)).comp blockSL

/-- The image of the actual SL₂(7) block in PSL₃(7). -/
def block : Subgroup Model := blockMap.range

/-- The image of diag(-1,-1,1) under the canonical quotient map. -/
def involution : Model := PSL3.projection (ZMod 7) (SL3.standardInvolution (ZMod 7))

/-- Conjugation by the standard projective involution. -/
def actor : MulAut Model := MulAut.conj involution

/-- The linear cover has its nontrivial odd center of order three. -/
theorem card_center_SL : Nat.card (center SL(3, ZMod 7)) = 3 := by
  rw [Atlas.ExceptionalSupport.card_sl_center, Nat.card_zmod]
  decide

/-- The SL₂ block loses no elements under projectivization. -/
theorem blockMap_injective : Function.Injective blockMap := by
  apply blockMap.ker_eq_bot_iff.mp
  apply le_bot_iff.mp
  intro x hx
  have hc : blockSL x ∈ center SL(3, ZMod 7) :=
    (QuotientGroup.eq_one_iff (blockSL x)).mp hx
  obtain ⟨r, _, hr⟩ := SpecialLinearGroup.mem_center_iff.mp hc
  have hr1 : r = 1 := by
    have he := congrArg (fun A : Matrix (Fin 3) (Fin 3) (ZMod 7) => A 2 2) hr
    change r = ↑((GeneralLinearGroup.det (SpecialLinearGroup.toGL x))⁻¹) at he
    simpa only [SpecialLinearGroup.coeToGL_det, inv_one, Units.val_one] using he
  have he : blockSL x = 1 := by
    apply Subtype.ext
    simpa [hr1] using hr.symm
  apply mem_bot.mpr
  apply SpecialLinearGroup.toGL_injective
  apply SL3.blockEmbedding_injective (ZMod 7)
  simpa [blockSL] using he

/-- A compatible isomorphism from SL₂(7) onto the projective block. -/
noncomputable def blockEquiv : SL(2, ZMod 7) ≃* block :=
  MonoidHom.ofInjective blockMap_injective

/-- The block is perfect, using a nontrivial square parameter in ZMod 7. -/
theorem block_perfect : Group.IsPerfect block := by
  let : Group.IsPerfect SL(2, ZMod 7) :=
    ⟨Matrix.SL2.commutator_eq_top (a := (2 : ZMod 7)) (by decide) (by decide)⟩
  exact Group.IsPerfect.ofSurjective blockMap.rangeRestrict_surjective

/-- The standard inner involution fixes the block pointwise. -/
theorem block_le_fixed : block ≤ actor.fixedSubgroup := by
  rintro _ ⟨x, rfl⟩
  apply (MulAut.mem_fixedSubgroup actor _).mpr
  have hc : blockSL x ∈ centralizer ({SL3.standardInvolution (ZMod 7)} : Set SL(3, ZMod 7)) := by
    rw [← SL3.blockEmbedding_range (ZMod 7) (by decide)]
    exact ⟨SpecialLinearGroup.toGL x, rfl⟩
  have he := congrArg (PSL3.projection (ZMod 7)) (mem_centralizer_singleton_iff.mp hc)
  change actor (blockMap x) = blockMap x
  change involution * blockMap x * involution⁻¹ = blockMap x
  have hcomm : blockMap x * involution = involution * blockMap x := by
    simpa only [blockMap, MonoidHom.comp_apply, involution, map_mul] using he
  rw [← hcomm, mul_inv_cancel_right]

/-- The block lies in the actual perfect residual of the fixed subgroup. -/
theorem block_le_fixedPerfectResidual : block ≤ MulAut.fixedPerfectResidual actor := by
  let := block_perfect
  exact le_map_solvableResidual_of_isPerfect block actor.fixedSubgroup block_le_fixed

/-- The standard projective element has square one. -/
theorem involution_sq : involution ^ 2 = 1 := by
  rw [involution, ← map_pow, SL3.standardInvolution_sq, map_one]

/-- A projective involution has an involution lift through the odd center. -/
theorem involution_lift (t : Model) (ht : orderOf t = 2) :
    ∃ x : SL(3, ZMod 7), orderOf x = 2 ∧ PSL3.projection (ZMod 7) x = t := by
  obtain ⟨x, rfl⟩ := PSL3.projection_surjective (ZMod 7) t
  have ht2 : PSL3.projection (ZMod 7) x ^ 2 = 1 := ht ▸ pow_orderOf_eq_one _
  have hx2 : x ^ 2 ∈ center SL(3, ZMod 7) := by
    apply (QuotientGroup.eq_one_iff _).mp
    change PSL3.projection (ZMod 7) (x ^ 2) = 1
    simpa only [map_pow] using ht2
  have hx6 : x ^ 6 = 1 := by
    have he := pow_card_eq_one' (x := (⟨x ^ 2, hx2⟩ : center SL(3, ZMod 7)))
    rw [card_center_SL] at he
    have he' := congrArg Subtype.val he
    simpa only [coe_pow, coe_one, ← pow_mul] using he'
  have he : PSL3.projection (ZMod 7) (x ^ 3) = PSL3.projection (ZMod 7) x := by
    rw [map_pow, pow_succ, ht2, one_mul]
  refine ⟨x ^ 3, orderOf_eq_prime ?_ ?_, he⟩
  · simpa only [← pow_mul] using hx6
  · intro hx
    have h1 : PSL3.projection (ZMod 7) x = 1 := by rw [← he, hx, map_one]
    simp [h1] at ht

/-- All projective involutions are conjugate to the standard representative. -/
theorem involution_conjugate (t : Model) (ht : orderOf t = 2) :
    ∃ g : Model, g * involution * g⁻¹ = t := by
  obtain ⟨x, hx, rfl⟩ := involution_lift t ht
  obtain ⟨s, hs⟩ := SL3.exists_standardInvolution_conjugator (ZMod 7) x hx (by decide)
  refine ⟨PSL3.projection (ZMod 7) s, ?_⟩
  simpa only [involution, map_mul, map_inv] using congrArg (PSL3.projection (ZMod 7)) hs

end Matrix.PSL3.SevenAction
