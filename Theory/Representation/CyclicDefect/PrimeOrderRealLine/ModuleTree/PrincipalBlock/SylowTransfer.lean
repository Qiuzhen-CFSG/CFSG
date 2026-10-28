module

public import Theory.Character.ModularBlock.FixedCosetTransfer
public import Theory.Character.ModularBlock.NormalizerRestriction
public import Theory.Character.ModularBlock.FinitePrimitiveCorner

/-!
# Recovery by transfer at a Sylow subgroup

A Sylow subgroup fixes only the identity coset of its normalizer. Consequently
relative transfer from the normalizer, followed by the Sylow Brauer map,
recovers every normalizer-fixed centralizer-algebra element. This is the
transfer input for the principal case of Brauer correspondence.

Source: Feit III.9 and V.6.2. The generic fixed-coset calculation is in
`ModularBlock.FixedCosetTransfer`.
-/

public section
noncomputable section
namespace Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.PrincipalBlock
open ModularBlock ModularBlock.NormalizerBrauerAction
open ModularBlock.RelativeTransferBrauer ModularBlock.BrauerThirdMain
variable {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]

omit [Fact p.Prime] in
private theorem sylow_fixed_coset (P : Sylow p G)
    (c : G ⧸ (Subgroup.normalizer (P : Set G)))
    (hc : c ∈ MulAction.fixedPoints (P : Subgroup G)
      (G ⧸ (Subgroup.normalizer (P : Set G)))) :
    c = (QuotientGroup.mk (1 : G) : G ⧸ (Subgroup.normalizer (P : Set G))) := by
  induction c using Quotient.inductionOn with
  | h x =>
    let Q : Subgroup G := (P : Subgroup G).map (MulAut.conj x⁻¹).toMonoidHom
    have hQN : Q ≤ (Subgroup.normalizer (P : Set G)) := by
      intro y hy
      obtain ⟨a, ha, rfl⟩ := hy
      have h := (MulAction.mem_fixedPoints.mp hc) (⟨a⁻¹, P.inv_mem ha⟩ : P)
      change (QuotientGroup.mk (a⁻¹ * x) : G ⧸ (Subgroup.normalizer (P : Set G))) =
        QuotientGroup.mk x at h
      have hh := QuotientGroup.eq.mp h
      simpa [MulAut.conj_apply, mul_assoc] using hh
    have hQP : Q ≤ (P : Subgroup G) := by
      have h := (P.isPGroup'.map (MulAut.conj x⁻¹).toMonoidHom).inf_normalizer_sylow P
      change Q ⊓ (Subgroup.normalizer (P : Set G)) = Q ⊓ (P : Subgroup G) at h
      rw [inf_eq_left.mpr hQN] at h
      exact inf_eq_left.mp h.symm
    have hQeq : Q = (P : Subgroup G) :=
      Subgroup.eq_of_le_of_card_ge hQP (le_of_eq
        (Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective).symm)
    have hx : x⁻¹ ∈ (Subgroup.normalizer (P : Set G)) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr hQeq
    exact QuotientGroup.eq.mpr (by simpa using hx)

/-- Transfer from the normalizer recovers a fixed centralizer element. -/
theorem sylow_transfer_recovery
    {K : Type*} [Field K] [CharP K p] (P : Sylow p G)
    (b : MonoidAlgebra K (Subgroup.centralizer (P : Set G)))
    (hfixed : ∀ n : (Subgroup.normalizer (P : Set G)),
      normalizerConjugate K (P : Subgroup G) n b = b) :
    DefectSupport.subgroupCentralizerRestriction K (P : Subgroup G)
      (relativeTransfer K (Subgroup.normalizer (P : Set G))
        (normalizerAlgebraEmbedding K (P : Subgroup G) b)) = b := by
  have hcenter := normalizerAlgebraEmbedding_mem_center_of_fixed
    (R := K) (P : Subgroup G) b hfixed
  have h := subgroupRestriction_relativeTransfer_eq_subtype_of_fixedTerms_zero
    (p := p) (R := K) (P : Subgroup G) P.isPGroup'
    (Subgroup.normalizer (P : Set G)) (P : Subgroup G).le_normalizer
    (normalizerAlgebraEmbedding K (P : Subgroup G) b) hcenter
    (by
      intro c hc hne
      exact (hne (sylow_fixed_coset P c hc)).elim)
  exact h.trans (subgroupRestriction_subgroupSubtypeMap_normalizerAlgebraEmbedding
    (R := K) (P : Subgroup G) b)

end Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.PrincipalBlock
