module
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.Complete
public import Theory.Representation.NormalInvariants
public import Theory.Representation.TwoDimensionalOddOrder

/-!
# Ree cover transport from the original modular action

The proved odd-primary covering theorem puts the center of an actual perfect
Ree cover in a two-group. Modular fixed vectors and irreducibility make it act
trivially; faithfulness then kills the center. The original quotient marking
therefore identifies the cover with the literal model. Scalar restriction
transports the binary involution estimate to every finite coefficient field.

This removes the independent center-triviality premise of the previous cover
reduction. The binary model estimate still belongs to the finite tensor
classification assembly. Sources: Aschbacher–Smith A.3.6 and I.1.1–4;
Guralnick–Malle II, Lemma 8.8.
-/

public section
open Subgroup Representation Theory.GroupTheory
namespace ReeF4.FixedSpaceEstimate
universe u v

/-- On the original faithful irreducible characteristic-two action, the proved
two-group center of a perfect Ree cover is trivial. -/
theorem center_eq_bot_of_faithful_irreducible {m : ℕ} (hm : 1 ≤ m)
    {L : Type u} [Group L] [Finite L] [IsQuasisimple L]
    (e : L ⧸ center L ≃* Model m)
    {E W : Type v} [Field E] [Finite E] [CharP E 2]
    [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    (σ : Representation E L W) [σ.IsIrreducible] (hf : Function.Injective σ) :
    center L = ⊥ := by
  have hcenter := CentralCovers.OddPrimary.center_isPGroup_of_quotient_equiv m hm e
  let : Nontrivial W := Subrepresentation.irreducible_module_nontrivial σ
  have hc : ringChar E = 2 := ringChar.eq E 2
  have hp : IsPGroup (ringChar E) (center L) := by simpa [hc] using hcenter
  obtain ⟨w, hw, hfix⟩ := pGroup_fix_nonzero_vector (by omega : ringChar E ≠ 0) hp
    (σ.comp (center L).subtype)
  have hk : center L ≤ σ.ker := by
    apply le_ker_of_normal_invariants_ne_bot σ (center L)
    intro hbot
    have hmem : w ∈ invariants (σ.comp (center L).subtype) := hfix
    rw [hbot, Submodule.mem_bot] at hmem
    exact hw hmem
  exact le_antisymm (hk.trans (le_of_eq (MonoidHom.ker_eq_bot σ hf))) bot_le

/-- The actual Ree cover transport needs only the binary model estimate; its
previous independent center-triviality premise is discharged by the action. -/
theorem coverInvolutionBound_of_binary_source {m : ℕ} (hm : 1 ≤ m)
    (hbinary : BinaryModelInvolutionBound.{v} m) : CoverInvolutionBound.{u,v} m := by
  intro L _ _ _ he E W _ _ _ _ _ _ _ σ hi hf t ht ht2
  let : σ.IsIrreducible := hi
  let : Module (ZMod 2) W := Module.compHom W (algebraMap (ZMod 2) E)
  let : IsScalarTower (ZMod 2) E W := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : FiniteDimensional (ZMod 2) E := Module.Finite.of_finite
  let : FiniteDimensional (ZMod 2) W := Module.Finite.trans (R := ZMod 2) E W
  obtain ⟨e⟩ := he
  have hcenter := center_eq_bot_of_faithful_irreducible hm e σ hf
  let f : L ≃* Model m := QuotientGroup.quotientBot.symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hcenter.symm).trans e)
  apply fixedCodim_ge_of_scalar_irreducibles σ hf (zpowers t) (10 * (2 * m + 1))
  intro U hU hUf
  exact binary_bound_of_equiv hbinary f U.toRepresentation hU hUf t ht ht2

end ReeF4.FixedSpaceEstimate
