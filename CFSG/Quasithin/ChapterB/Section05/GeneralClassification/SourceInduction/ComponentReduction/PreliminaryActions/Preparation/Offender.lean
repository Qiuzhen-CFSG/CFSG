module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.LocalContracts
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Minimal offenders on the literal seed quotient

The map from LA/C_LA(U) into Aut_{N_G(U)}(U) is explicitly constructed and
injective. Its image of A⁺ is precisely Aut_A(U), so the proved B.1.5/B.7.1
restriction theorem gives minimality for the literal subgroup A⁺. The
transport compares every subgroup's weight and retains equal-weight
minimality; an arbitrary isomorphism of unmarked actors is not used.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.1.5(2), printed p.69; B.5.9, printed p.107.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions.Preparation
variable {G D V : Type*} [Group G] [Group D] [AddCommGroup V] [Module (ZMod 2) V]

private theorem best_map (σ : Representation (ZMod 2) D V) (f : G →* D)
    (hf : Function.Injective f) {A : Subgroup G} (hA : IsBestOffender (σ.comp f) A) :
    IsBestOffender σ (A.map f) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsElementaryAbelian 2 A := hA.1.2
  refine ⟨⟨?_, IsElementaryAbelian.map f⟩, ?_⟩
  · exact fun h => hA.1.1 ((Subgroup.map_eq_bot_iff_of_injective A hf).mp h)
  · intro B hB
    let C := A ⊓ B.comap f
    have hm : C.map f = B := by
      apply le_antisymm
      · rintro _ ⟨x,hx,rfl⟩
        exact hx.2
      · intro b hb
        obtain ⟨a,ha,rfl⟩ := hB hb
        exact ⟨a,⟨ha,hb⟩,rfl⟩
    rw [← hm, ← weight_comp_map σ f hf, ← weight_comp_map σ f hf]
    exact hA.2 C inf_le_left

theorem minimal_of_injective_image (σ : Representation (ZMod 2) D V) (f : G →* D)
    (hf : Function.Injective f) {A : Subgroup G} (hAe : IsElementaryAbelian 2 A)
    (hA : IsMinimalBestOffender σ (A.map f)) :
    IsMinimalBestOffender (σ.comp f) A := by
  have hb : IsBestOffender (σ.comp f) A := by
    refine ⟨⟨?_,hAe⟩, ?_⟩
    · intro h
      exact hA.1.1.1 (by rw [h,Subgroup.map_bot])
    · intro B hBA
      rw [weight_comp_map σ f hf, weight_comp_map σ f hf]
      exact hA.1.2 _ (Subgroup.map_mono hBA)
  refine ⟨hb, ?_⟩
  intro B hB hBA
  apply Subgroup.map_injective hf
  apply hA.2 _ (best_map σ f hf hB)
  refine ⟨Subgroup.map_mono hBA.1, ?_⟩
  simpa only [weight_comp_map σ f hf] using hBA.2

variable (ρ : Representation (ZMod 2) G V)

/-- The literal kernel quotient embeds in the action image of the stabilizer
of U. This is the map used to transport B.1.5 to LA/C_LA(U). -/
noncomputable def seedActionEmbedding {L A : Subgroup G} (hLA : ⁅L,A⁆ = L) :
    SeedQuotient ρ hLA →* subspaceActionImage ρ (naturalSeedSpace ρ L A) :=
  QuotientGroup.lift _
    ((subspaceActionHom ρ (naturalSeedSpace ρ L A)).comp
      (Subgroup.inclusion (seedSpace_stable ρ hLA))) (by
        intro g hg
        apply subspaceImageRepresentation_injective ρ (naturalSeedSpace ρ L A)
        exact MonoidHom.mem_ker.mp hg)

@[simp] theorem seedActionEmbedding_apply {L A : Subgroup G} (hLA : ⁅L,A⁆ = L)
    (g : (L ⊔ A : Subgroup G)) :
    seedActionEmbedding ρ hLA (seedQuotientMap ρ hLA g) =
      subspaceActionHom ρ (naturalSeedSpace ρ L A) ⟨g,seedSpace_stable ρ hLA g.property⟩ := rfl

theorem seedActionEmbedding_action {L A : Subgroup G} (hLA : ⁅L,A⁆ = L) :
    (subspaceImageRepresentation ρ (naturalSeedSpace ρ L A)).comp
      (seedActionEmbedding ρ hLA) = seedQuotientAction ρ hLA := by
  apply MonoidHom.ext
  intro q
  obtain ⟨g,rfl⟩ := (QuotientGroup.mk'_surjective
    (seedSubrepresentation ρ hLA).toRepresentation.ker) q
  rfl

theorem seedActionEmbedding_injective {L A : Subgroup G} (hLA : ⁅L,A⁆ = L) :
    Function.Injective (seedActionEmbedding ρ hLA) := by
  intro x y h
  apply seedQuotientAction_faithful ρ hLA
  rw [← seedActionEmbedding_action ρ hLA]
  exact congrArg (subspaceImageRepresentation ρ (naturalSeedSpace ρ L A)) h

theorem seedActionEmbedding_offender {L A : Subgroup G} (hLA : ⁅L,A⁆ = L) :
    (seedOffenderImage ρ hLA).map (seedActionEmbedding ρ hLA) =
      restrictedSubgroup ρ (naturalSeedSpace ρ L A) A := by
  ext x
  constructor
  · rintro ⟨q, ⟨g,hg,rfl⟩,rfl⟩
    exact ⟨⟨g,seedSpace_stable ρ hLA g.property⟩,hg,rfl⟩
  · rintro ⟨g,hg,rfl⟩
    refine ⟨seedQuotientMap ρ hLA ⟨g,(le_sup_right : A ≤ L ⊔ A) hg⟩,
      ⟨⟨g,(le_sup_right : A ≤ L ⊔ A) hg⟩,hg,rfl⟩,rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- B.1.5 minimality on Aut_A(U), transported to the actual quotient image. -/
theorem seedOffender_minimal [Finite G] [Module.Finite (ZMod 2) V]
    {A L : Subgroup G} (hf : Function.Injective ρ) (hA : IsMinimalBestOffender ρ A)
    (hLA : ⁅L,A⁆ = L) (hm : subspaceCommutator ρ (naturalSeedSpace ρ L A) A ≠ ⊥) :
    IsMinimalBestOffender (seedQuotientAction ρ hLA) (seedOffenderImage ρ hLA) := by
  have hs : A ≤ subspaceStabilizer ρ (naturalSeedSpace ρ L A) :=
    le_sup_right.trans (seedSpace_stable ρ hLA)
  have h := (ChapterB.source_lemma_B_7_1_2 ρ (naturalSeedSpace ρ L A) hf hA
    (fun a ha w hw => (hs ha w).2 hw) hm).1
  rw [← seedActionEmbedding_offender ρ hLA] at h
  let : IsElementaryAbelian 2 A := hA.1.1.2
  let : IsElementaryAbelian 2 (A.subgroupOf (L ⊔ A)) :=
    IsElementaryAbelian.subgroupOf (show A ≤ L ⊔ A from le_sup_right)
  have he : IsElementaryAbelian 2 (seedOffenderImage ρ hLA) :=
    IsElementaryAbelian.map (seedQuotientMap ρ hLA)
  simpa only [seedActionEmbedding_action] using
    minimal_of_injective_image _ (seedActionEmbedding ρ hLA)
      (seedActionEmbedding_injective ρ hLA) he h
end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions.Preparation
