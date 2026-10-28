module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.Pair
public import Theory.GroupTheory.SplitNormalComplementQuotient

/-!
# The subgroup endpoint of the local residual analysis

The last paragraph of GLS, Volume 4, Chapter 2, Section 17 uses two
subgroup conclusions: the two-point stabilizer `D` has even order and a
normal two-complement (Section 16), and it complements `O₂(M)` inside `M`
(Proposition 17.6). Thus `M` maps onto the nontrivial two-group
`D/O_{2'}(D)`, forcing its two-residual to be proper.

This module proves that quotient argument. The Section 16 and Section 17
subgroup conclusions remain explicit premises; it does not yet assert the
unconditional local residual theorem. In particular, no model recognition
or rational counting identity is assumed to have been proved here.
-/

noncomputable section

namespace BenderSuzuki.ZD

variable {G : Type*} [Group G] [Finite G]

/-- The actual subgroup facts after Proposition 17.6 give a proper
two-residual. The quotient used is `D/O_{2'}(D)`, not `D/O²(D)`. -/
public theorem twoResidual_ne_top_of_split_pair
    {M : Subgroup G} {t : G}
    (hsplit : (residualPairIn M t).IsComplement' (pCore 2 M))
    (hcomp : HasNormalPComplement 2 (residualPairIn M t))
    (heven : 2 ∣ Nat.card (residualPairIn M t)) :
    External.hallPResidual 2 M ≠ ⊤ := by
  let D := residualPairIn M t
  let Q := D ⧸ pPrimeCore 2 D
  let : Nontrivial Q := nontrivial_quotient_pPrimeCore_of_dvd_card heven
  let f : M →* Q := hsplit.toPrimeComplementQuotient 2
  have hf : Function.Surjective f := hsplit.toPrimeComplementQuotient_surjective 2
  have hQ : IsPGroup 2 Q :=
    isPGroup_quotient_pPrimeCore_of_hasNormalPComplement 2 D hcomp
  have hker := External.hallPResidual_le_ker_of_isPGroup f hQ
  intro htop
  rw [htop] at hker
  obtain ⟨q, hq⟩ := exists_ne (1 : Q)
  obtain ⟨x, rfl⟩ := hf q
  exact hq (MonoidHom.mem_ker.mp (hker (Subgroup.mem_top x)))

/-- Conditional assembly with independent Section 16 and Section 17
outputs. The owner must construct both premises from the residual setup. -/
public theorem twoResidual_ne_top_of_local_steps
    {Z : Set G} {M : Subgroup G}
    (local_complement : ∀ t ∈ Z, t ∉ M →
      HasNormalPComplement 2 (residualPairIn M t) ∧
        2 ∣ Nat.card (residualPairIn M t))
    (splitting : ∃ t ∈ Z, t ∉ M ∧
      (residualPairIn M t).IsComplement' (pCore 2 M)) :
    External.hallPResidual 2 M ≠ ⊤ := by
  obtain ⟨t, htZ, htM, hsplit⟩ := splitting
  obtain ⟨hcomp, heven⟩ := local_complement t htZ htM
  exact twoResidual_ne_top_of_split_pair hsplit hcomp heven

end BenderSuzuki.ZD
