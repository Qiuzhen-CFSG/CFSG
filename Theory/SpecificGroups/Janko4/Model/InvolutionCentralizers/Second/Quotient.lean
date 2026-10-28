module

public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.Second.LocalKernel
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.Second.PairIdentification
public import Mathlib.GroupTheory.GroupExtension.Defs

/-!
# The local E2048.Aut(M22) centralizer extension

Restrict the certified star quotient to the stabilizer of the seed pair.
Its kernel is precisely the embedded elementary normal kernel. The first
isomorphism theorem supplies the quotient equivalence and exact sequence.
Self-centralization makes the resulting action on that kernel faithful.

Source: Aschbacher--Smith 16.1.5(9), printed p.1172; GLS3 Table 5.3i.
No splitting is asserted.
-/

@[expose] public section
noncomputable section
namespace Janko4.InvolutionCentralizers.Second
open Subgroup Cardinality Cardinality.QuotientCount LocalStructure Sporadic.Mathieu

attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernelSeed localKernel

/-- The geometric quotient onto the actual automorphism group of native M22. -/
def toAutM22 : localCentralizer →* MulAut M22 :=
  starPairEquivAutM22.toMonoidHom.comp toStarPair

theorem toAutM22_surjective : Function.Surjective toAutM22 :=
  starPairEquivAutM22.surjective.comp toStarPair_surjective

theorem toStarPair_ker : toStarPair.ker = kernel := by
  ext g
  change (⟨starHom g.val, _⟩ : starPairStabilizer) = 1 ↔ g.val ∈ max1Kernel
  rw [Subtype.ext_iff]
  change Image.actionImageEquivStarGroup _ _ ((action _ _).rangeRestrict g.val) = 1 ↔ _
  rw [map_eq_one_iff _ (Image.actionImageEquivStarGroup _ _).injective]
  change (⟨action _ _ g.val, _⟩ : ActionImage _ _) = 1 ↔ _
  rw [Subtype.ext_iff]
  exact SetLike.ext_iff.mp (action_ker_eq_localKernel _ _) g.val

theorem toAutM22_ker : toAutM22.ker = kernel := by
  ext g
  change starPairEquivAutM22 (toStarPair g) = 1 ↔ _
  rw [map_eq_one_iff _ starPairEquivAutM22.injective]
  exact SetLike.ext_iff.mp toStarPair_ker g

/-- The local order follows from its actual pair quotient, independently of
any full-ambient centralizer bound. -/
theorem localCentralizer_card : Nat.card localCentralizer = 1816657920 := by
  have hc := kernel.card_mul_index
  rw [kernel_card] at hc
  have hi : kernel.index = 887040 := by
    rw [← toStarPair_ker, index_ker,
      MonoidHom.range_eq_top_of_surjective _ toStarPair_surjective, card_top]
    exact (Nat.card_congr starPairEquivNative.toEquiv).trans
      MathieuCode.m22PairStabilizer_card
  rw [hi] at hc
  exact hc.symm

/-- A quotient equivalence constructed from the actual pair action. -/
def localQuotientEquivAutM22 : (localCentralizer ⧸ kernel) ≃* MulAut M22 :=
  (QuotientGroup.quotientMulEquivOfEq toAutM22_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective toAutM22 toAutM22_surjective)

/-- The quotient marking retains the original local conjugation action. -/
theorem localQuotientEquivAutM22_mk (g : localCentralizer) :
    localQuotientEquivAutM22 (QuotientGroup.mk' kernel g) = toAutM22 g := rfl

/-- The exact sequence with the actual embedded kernel of order 2^11. -/
def localExtension : GroupExtension kernel localCentralizer (MulAut M22) where
  inl := kernel.subtype
  rightHom := toAutM22
  inl_injective := kernel.subtype_injective
  range_inl_eq_ker_rightHom := by rw [range_subtype, toAutM22_ker]
  rightHom_surjective := toAutM22_surjective

/-- Intrinsic conjugation on the kernel, including its multiplication. -/
def conjugation : localCentralizer →* MulAut kernel := MulAut.conjNormal

theorem conjugation_ker : conjugation.ker = kernel := by
  trans centralizer (kernel : Set localCentralizer)
  · ext g
    constructor
    · intro hg u hu
      have he := congrArg (fun a : MulAut kernel => ((a ⟨u, hu⟩ : kernel) : localCentralizer)) hg
      change g * u * g⁻¹ = u at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    · intro hg
      apply MulEquiv.ext
      intro u
      apply Subtype.ext
      change g * u.val * g⁻¹ = u.val
      exact mul_inv_eq_iff_eq_mul.mpr (hg u.val u.property).symm
  · exact kernel_selfCentralizing

/-- The kernel quotient acts faithfully on the embedded elementary group. -/
def quotientAction : (localCentralizer ⧸ kernel) →* MulAut kernel :=
  (QuotientGroup.kerLift conjugation).comp
    (QuotientGroup.quotientMulEquivOfEq conjugation_ker.symm).toMonoidHom

theorem quotientAction_injective : Function.Injective quotientAction :=
  (QuotientGroup.kerLift_injective conjugation).comp
    (QuotientGroup.quotientMulEquivOfEq conjugation_ker.symm).injective

theorem quotientAction_mk (g : localCentralizer) (u : kernel) :
    (quotientAction (QuotientGroup.mk' kernel g) u : localCentralizer) =
      g * u.val * g⁻¹ := rfl

/-- The faithful Aut(M22) action induced by this specific extension. -/
def autM22Action : MulAut M22 →* MulAut kernel :=
  quotientAction.comp localQuotientEquivAutM22.symm.toMonoidHom

theorem autM22Action_injective : Function.Injective autM22Action :=
  quotientAction_injective.comp localQuotientEquivAutM22.symm.injective

theorem autM22Action_apply (g : localCentralizer) (u : kernel) :
    (autM22Action (toAutM22 g) u : localCentralizer) = g * u.val * g⁻¹ := by
  rw [← localQuotientEquivAutM22_mk]
  change (quotientAction
    (localQuotientEquivAutM22.symm (localQuotientEquivAutM22 _)) u : localCentralizer) = _
  rw [localQuotientEquivAutM22.symm_apply_apply]
  exact quotientAction_mk g u

end Janko4.InvolutionCentralizers.Second
