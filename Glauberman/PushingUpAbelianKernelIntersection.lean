module
public import Glauberman.MaximumAbelianKernelIntersection
public import Glauberman.PushingUpAbelianReplacement

/-!
# Niles7.5 in the original rank-one group

The sharp replacement theorem7.4 supplies the maximum abelian family needed
by the intersection selection theorem. This specializes to the literal
O₂(H), its central omega subgroup, and the largest invariant ambient-normal
kernel of the original Sylow subgroup. The natural-module theorem2.9 remains
an independent input through its lower bound four on fixed-space index.
The arbitrary original PSL2(4) kernel is retained.

Source: Niles, *Pushing-up in finite groups* (1979), Lemmas7.4–7.5, printed p.61.
-/

public section
open Subgroup
namespace Glauberman
variable {H : Type*} [Group H] [Finite H]

/-- The actual Niles7.5 consumer, with the original arbitrary PSL2(4)
quotient and the literal two-core. The natural-module producer supplies
only the lower fixed-space index used in7.4. -/
theorem pushingUp_exists_maximum_abelian_kernel_intersection
    {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 4) (S : Sylow 2 H)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal]
    (e : (H ⧸ K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hno : Theory.GroupTheory.NoCharacteristicNormal (S : Subgroup H))
    (hlower : ∀ A : Subgroup H, A ∈ thompsonAbelianSubgroups (S : Subgroup H) →
      ¬ A ≤ pCore 2 H →
      4 ≤ (omegaCenterIn (pCore 2 H) ⊓ centralizer (A : Set H)).relIndex
        (omegaCenterIn (pCore 2 H)))
    (α : MulAut S)
    (hVN : omegaCenterIn (pCore 2 H) ≤
      (NilesRankOneKernel.invariantNormalKernel (S : Subgroup H) α).map
        (S : Subgroup H).subtype) :
    ∃ A : Subgroup H, A ∈ thompsonAbelianSubgroups (S : Subgroup H) ∧
      ¬ A ≤ pCore 2 H ∧
      A ⊓ pCore 2 H = A ⊓
        (NilesRankOneKernel.invariantNormalKernel (S : Subgroup H) α).map
          (S : Subgroup H).subtype := by
  obtain ⟨hex,hr⟩ := pushingUp_exists_maximum_abelian_replacement hF S hu K e hno hlower
  obtain ⟨A,hA,hAQ⟩ := hex
  have hfamily := (pushingUp_maximum_abelian_replacement hF S hu K e A hA
    (hlower A hA hAQ)).2.2.2.2.2.2
  have hNQ : (NilesRankOneKernel.invariantNormalKernel (S : Subgroup H) α).map
      (S : Subgroup H).subtype ≤ pCore 2 H := by
    have hp := S.isPGroup'.of_injective
      (inclusion (map_subtype_le (NilesRankOneKernel.invariantNormalKernel (S : Subgroup H) α)))
      (inclusion_injective _)
    exact le_sSup ⟨inferInstance,hp⟩
  apply exists_maximum_abelian_kernel_intersection (S : Subgroup H) α (pCore 2 H)
    (omegaCenterIn (pCore 2 H)) (pCore_isPGroup.le_sylow_of_normal S) hfamily
    ⟨A,hA,hAQ⟩ _ hNQ hVN
  intro B hB hBQ
  obtain ⟨_,hb,_,_,hv⟩ := hr B hB hBQ
  exact ⟨hb,hv⟩

end Glauberman
