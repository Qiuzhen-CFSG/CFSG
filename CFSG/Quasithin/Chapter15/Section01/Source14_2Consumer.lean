module

public import CFSG.Quasithin.Chapter15.Section01.SourceReduction
public import CFSG.Quasithin.Chapter14.Section02.OriginalMovement

/-!
# The selected rank-two branch reaches the original 14.2.14 consumer

The selected-source reduction has three alternatives.  In its rank-two
alternative the literal card and quotient data are exactly the inputs of the
original second-amalgam theorem, so this module applies that theorem directly
and leaves the orthogonal and Baumann branches unchanged.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterB
open Chapter14.SourcePreliminaries Chapter15.Section03 Chapter14.Section02
variable {G : Type*} [Group G] [Finite G]

theorem source_selected_reduction_with_14_2_14
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {Mc : Subgroup G}
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    ∃ M : Subgroup G, IsOrderingMaximal T M ∧ M ≠ Mc ∧
      ((∃ e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
          Equiv.Perm (Fin 3),
          Nat.card (localModule T M) = 4 ∧
          Function.Injective e.toEquiv ∧
          ∀ H ∈ Chapter3.HStar (T : Subgroup G) M,
            let Y := sourceResidual M Mc
            let K := (pResidual 2 H).map H.subtype
            let S₂ := Y.pCoreIn 2 ⊔ ((T : Subgroup G) ⊓ K)
            Y = ⁅Y,S₂⁆ ∧
              Nonempty (((Y ⊔ S₂ : Subgroup G) ⧸ pCore 2 (Y ⊔ S₂ : Subgroup G)) ≃*
                Equiv.Perm (Fin 3)) ∧
              (T : Subgroup G) ⊓ (Y ⊔ S₂) = S₂ ∧
              Chapter1.IsSylowIn 2 S₂ (Y ⊔ S₂)) ∨
        Nonempty (NaturalOrthogonalAction M (localModule T M)) ∨
        (elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G) ∧
          localModule T M ≤ thompsonAlpha (T : Subgroup G) ∧
          baumann (T : Subgroup G) =
            baumann ((T : Subgroup G) ⊓ centralizer (localModule T M : Set G)) ∧
          (baumann (T : Subgroup G)).characteristicNormalizerClosure ≤ M ∧
          ∀ H ∈ Chapter3.HStar (T : Subgroup G) M,
            ChapterB.IsMinimalParabolicOver T H ∧
            IsSQTK KnownSimple.IsKnownSimple H ∧
            generalizedFitting H = pCore 2 H)) := by
  obtain ⟨M, hM, hne, _, halt⟩ := source_selected_reduction hG T hempty hu hmany
  refine ⟨M, hM, hne, ?_⟩
  rcases halt with h | h | h
  · rcases h with ⟨hcard, ⟨e⟩, _⟩
    left
    refine ⟨e, hcard, e.toEquiv.injective, ?_⟩
    intro H hH
    exact source_lemma_14_2_14 hG T hempty hM hu hmany hcard e H hH
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

end CFSG.Quasithin.Chapter15.Section01
