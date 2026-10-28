module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.NativeSource.Exceptional.Stabilizer
public import Mathlib.Algebra.Group.Action.TransferInstance

/-!
# Field coordinates for the actual quotient action

A root-group equivalence transfers the square-coordinate action to the binary
field. Faithfulness and transitivity are inherited from the literal M/O₂(M)
action; the formula on the image of every original m ∈ M is retained.

Source: GLS IV, Chapter 2, Lemma 15.7, exceptional equality branch.
-/

noncomputable section
namespace BenderSuzuki.ZD.LinearExclusion.Exceptional
open Subgroup Theory.GroupTheory PFAppendixIII
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {n : ℕ} (s : ExceptionalLocalStructure Z M z t n)
  (d : Context Z M z t n)
  (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 2)
  (hR : Nat.card (linearCentralizerClosure M z t) = 2 * (2 ^ n) ^ 2)
  (hRV : linearCentralizerClosure M z t = pCore 2 M)
local notation "A" => Subgroup.subgroupOf (closure (Z ∩ (M : Set G))) M
local notation "V" => pCore 2 M
local notation "𝔽" => BinaryGaloisField n
variable (eA : (closure (Z ∩ (M : Set G))).subgroupOf M ≃* Multiplicative (BinaryGaloisField n))

/-- The source field action is the original quotient action in root coordinates. -/
@[expose, instance_reducible] public def fieldAction : MulAction (M ⧸ V) 𝔽 := by
  let := quotientAction s d hJ hR hRV
  exact (eA.toEquiv.trans Multiplicative.toAdd).symm.mulAction (M ⧸ V)

public theorem fieldAction_smul_mk (m : M) (a : A) :
    let := pointAction s d hR hRV
    let := fieldAction s d hJ hR hRV eA
    QuotientGroup.mk' V m • (eA a).toAdd = (eA (m • a)).toAdd := by
  let := pointAction s d hR hRV
  let := fieldAction s d hJ hR hRV eA
  change (eA ((quotientPermutation s d hJ hR hRV (QuotientGroup.mk' V m))
    (eA.symm (eA a)))).toAdd = _
  rw [eA.symm_apply_apply]
  rfl

public theorem fieldAction_faithful :
    let := fieldAction s d hJ hR hRV eA
    FaithfulSMul (M ⧸ V) 𝔽 := by
  let := quotientAction s d hJ hR hRV
  let := fieldAction s d hJ hR hRV eA
  constructor
  intro g k he
  apply quotientPermutation_injective s d hJ hR hRV
  apply Equiv.ext
  intro a
  apply eA.injective
  apply Multiplicative.toAdd.injective
  have hh := he (eA a).toAdd
  change (eA ((quotientPermutation s d hJ hR hRV g) (eA.symm (eA a)))).toAdd =
    (eA ((quotientPermutation s d hJ hR hRV k) (eA.symm (eA a)))).toAdd at hh
  simpa only [eA.symm_apply_apply] using hh

public theorem fieldAction_pretransitive :
    let := fieldAction s d hJ hR hRV eA
    MulAction.IsPretransitive (M ⧸ V) 𝔽 := by
  let := quotientAction s d hJ hR hRV
  let : MulAction.IsPretransitive (M ⧸ V) A := quotientAction_pretransitive s d hJ hR hRV
  let := fieldAction s d hJ hR hRV eA
  constructor
  intro a b
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (M ⧸ V)
    (eA.symm (Multiplicative.ofAdd a)) (eA.symm (Multiplicative.ofAdd b))
  refine ⟨g, ?_⟩
  change (eA ((quotientPermutation s d hJ hR hRV g)
    (eA.symm (Multiplicative.ofAdd a)))).toAdd = b
  change (quotientPermutation s d hJ hR hRV g)
    (eA.symm (Multiplicative.ofAdd a)) = eA.symm (Multiplicative.ofAdd b) at hg
  rw [hg, eA.apply_symm_apply]
  rfl

end BenderSuzuki.ZD.LinearExclusion.Exceptional
