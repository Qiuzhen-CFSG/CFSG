module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.Preparation.FixedCore
public import Theory.Representation.BinaryOffender.IrreducibleExistence

/-!
# Generation of the literal B.5.9 seed

For a perfect actor L and an L-invariant space X, the quotient by
[[X,L],L] makes [X,L] central. Perfectness then makes X central in that
quotient, proving [[X,L],L]=[X,L]. Apply this to C_V(O₂(LA)), and map the
result through the actual action quotient LA/C_LA(U). Thus [U,L⁺]=U
before any comparison with [V,L] or selection of a B.5.1 row.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.9, printed p.107, the seed in the first paragraph of the proof.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions
open QuasisimpleSource
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- Perfectness makes the commutator operation idempotent on invariant spaces. -/
theorem perfect_seed_idempotent (L : Subgroup G) [Group.IsPerfect L]
    (I : Submodule (ZMod 2) V) (hI : L ≤ subspaceStabilizer ρ I) :
    subspaceCommutator ρ (subspaceCommutator ρ I L) L = subspaceCommutator ρ I L := by
  let J := subspaceCommutator ρ I L
  let D := subspaceCommutator ρ J L
  have hD : L ≤ subspaceStabilizer ρ D := subspaceCommutator_invariant ρ J L
  let Drep := invariantSubspace ρ L D hD
  let qρ := Drep.quotientRepresentation
  let QI := I.map Drep.toSubmodule.mkQ
  have hQI : (⊤ : Subgroup L) ≤ subspaceStabilizer qρ QI := by
    apply le_subspaceStabilizer
    rintro l _ _ ⟨v, hv, rfl⟩
    exact ⟨ρ l v, (hI l.property v).2 hv, rfl⟩
  have hQC : subspaceCommutator qρ QI ⊤ ≤ fixedSpace qρ ⊤ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, _, _, ⟨v, hv, rfl⟩, rfl⟩
    intro k
    change qρ k.val (qρ x (Drep.toSubmodule.mkQ v) - Drep.toSubmodule.mkQ v) =
      qρ x (Drep.toSubmodule.mkQ v) - Drep.toSubmodule.mkQ v
    rw [map_sub]
    change Drep.toSubmodule.mkQ (ρ k.val (ρ x v)) - Drep.toSubmodule.mkQ (ρ k.val v) =
      Drep.toSubmodule.mkQ (ρ x v) - Drep.toSubmodule.mkQ v
    rw [← map_sub, ← map_sub]
    apply (Submodule.Quotient.eq D).mpr
    exact Submodule.subset_span
      ⟨k.val, k.val.property, ρ x v - v,
        Submodule.subset_span ⟨x.val, x.property, v, hv, rfl⟩, by
          simp only [map_sub]⟩
  have hfix := le_fixedSpace_of_commutator_le_fixedSpace qρ (⊤ : Subgroup L) QI hQI hQC
  apply le_antisymm (subspaceCommutator_le_of_invariant ρ (subspaceCommutator_invariant ρ I L))
  apply Submodule.span_le.mpr
  rintro _ ⟨l, hl, v, hv, rfl⟩
  have he := hfix (show Drep.toSubmodule.mkQ v ∈ QI from ⟨v, hv, rfl⟩) ⟨⟨l, hl⟩, mem_top _⟩
  apply (Submodule.Quotient.mk_eq_zero D).mp
  change Drep.toSubmodule.mkQ (ρ l v - v) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr he

/-- The component generates all of the literal seed, independently of the source row. -/
theorem seedQuotient_moved_eq_top {A L : Subgroup G} (hLA : ⁅L,A⁆ = L)
    (hL : IsComponent G L) :
    moved (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA) = ⊤ := by
  let : IsQuasisimple L := hL.2
  have hi := perfect_seed_idempotent ρ L (fixedSpace ρ (localTwoCore L A))
    (le_sup_left.trans (Preparation.fixedCore_stable ρ L A))
  apply Submodule.map_injective_of_injective (seedSubrepresentation ρ hLA).toSubmodule.subtype_injective
  rw [Submodule.map_top, Submodule.range_subtype]
  apply le_antisymm
  · exact Submodule.map_subtype_le _ _
  · change naturalSeedSpace ρ L A ≤ _
    unfold naturalSeedSpace
    rw [← hi]
    apply Submodule.span_le.mpr
    rintro _ ⟨l, hl, v, hv, rfl⟩
    let l₀ : (L ⊔ A : Subgroup G) := ⟨l, (le_sup_left : L ≤ L ⊔ A) hl⟩
    exact ⟨seedQuotientAction ρ hLA (seedQuotientMap ρ hLA l₀) ⟨v, hv⟩ - ⟨v, hv⟩,
      Submodule.subset_span ⟨seedQuotientMap ρ hLA l₀, ⟨l₀, hl, rfl⟩,
        ⟨v, hv⟩, Submodule.mem_top, rfl⟩, rfl⟩
end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions
