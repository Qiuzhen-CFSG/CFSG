module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Transport
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.ActionGeometry
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Residual

/-!
# The characteristic-two branch of the mixed-factor argument

These proofs construct `Vᵢ=⟨Zᴵ⟩`, its elementary abelian group structure,
its exact two-core centralizer, and its faithful quotient representation.
They construct an actual FF-offender from a factor moving `Z`, and identify
the pointwise stabilizer of the order-four seed. The final lifting argument
uses both factor commutator identities to normalize `O²(Y₁O₂(I))=Y₁` after
an actual `I/O₂(I) ≃ S₃ × S₃` identification.

The quotient identification is not proved here. The remaining source step
must place the factor images in the best-offender generated subgroup and
compare all genuine B.5.6 and F.6.18 alternatives, with their full group,
module and field restrictions. The theorem below is only the final lifting
implication; it is not a completed assertion of the branch contradiction.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, 15.4.18, printed p.1163.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch
open Subgroup Stellmacher
variable {G : Type*} [Group G] [Finite G]

/-- An actual quotient identification contradicts the previously established outside factor. -/
theorem contradiction_of_symmetricThreeProduct_quotient
    (T : Sylow 2 G) (I Y₁ Y₂ : Subgroup G) (P : Sylow 2 I)
    (hPT : (P : Subgroup I).map I.subtype ≤ (T : Subgroup G))
    (hB : ChapterB.baumann (T : Subgroup G) ≤ (P : Subgroup I).map I.subtype)
    (h₁I : Y₁ ≤ I) (h₂I : Y₂ ≤ I)
    (hperfect : IsPPerfect 2 Y₁)
    (hTnorm : (T : Subgroup G) ≤ normalizer (Y₁ : Set G))
    (h₁ : Y₁ = ⁅Y₁, elementaryAbelianMaxJ (T : Subgroup G)⁆)
    (h₂ : Y₂ = ⁅Y₂, elementaryAbelianMaxJ (T : Subgroup G)⁆)
    (hnot : ¬ Y₂ ≤ normalizer (Y₁ : Set G))
    (e : (I ⧸ pCore 2 I) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) : False := by
  have hJ := thompson_sylow_image_of_baumann I T P hB
  have h₁' := factor_commutator_subgroupOf I Y₁ _ _ h₁I hJ h₁
  have h₂' := factor_commutator_subgroupOf I Y₂ _ _ h₂I hJ h₂
  have hp : IsPPerfect 2 (Y₁.subgroupOf I) := hperfect.of_surjective
    (subgroupOfEquivOfLe h₁I).symm.toMonoidHom (subgroupOfEquivOfLe h₁I).symm.surjective
  have hQnorm : pCore 2 I ≤ normalizer (Y₁.subgroupOf I : Set I) := by
    rw [← subgroupOf_normalizer_eq h₁I]
    intro x hx
    exact hTnorm (hPT (mem_map_of_mem I.subtype (pCore_isPGroup.le_sylow_of_normal P hx)))
  have hn := normalizes_factor_of_symmetricThreeProduct_quotient (pCore 2 I)
    (Y₁.subgroupOf I) (Y₂.subgroupOf I) (elementaryAbelianMaxJ (P : Subgroup I))
    pCore_isPGroup hp hQnorm h₁' h₂' e
  exact hnot (normalizer_subgroupOf_lift I Y₁ Y₂ h₁I h₂I hn)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch
