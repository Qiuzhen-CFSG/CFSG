module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Exchanged

/-!
# The intrinsic E.2 marking on the original local action

The marked component in the actual subgroup H is sent through H's inclusion.
Subgroup pullback cancels this inclusion, so the two source-image descriptions
and their Borel overlaps agree. In the exchanged branch J = O₂(H) then
transports that same Borel pair to the action quotient.

Source: Aschbacher–Smith E.2.2(1), pp.215–216; 15.3.65, p.1152.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Exchanged
open RepresentationReduction.SourceRestrictions.Cases.Exchanged
variable {G : Type*} [Group G] {H M : Subgroup G} {K : Subgroup H}

/-- The actual inclusion of the intrinsic component preserves its marked Borel. -/
theorem modelBorelPair_of_intrinsic {D : Type*} [Group D] {B : Subgroup D}
    (h : ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.ModelBorelPair (M.subgroupOf H) K B) :
    BorelReduction.SourceCases.ModelBorelPair H M (K.map H.subtype) B := by
  unfold BorelReduction.SourceCases.ModelBorelPair
    BorelReduction.SourceCases.componentOverlap BorelReduction.sourceImage
  have hk : (K.map H.subtype).subgroupOf H = K :=
    comap_map_eq_self_of_injective H.subtype_injective K
  have hov : (M ⊓ K.map H.subtype).subgroupOf H = M.subgroupOf H ⊓ K := by
    simp only [subgroupOf,comap_inf,comap_map_eq_self_of_injective H.subtype_injective]
  rw [hk,hov]
  exact h

/-- The odd rank-one source model is unchanged on the ambient component map. -/
theorem exchangedModel_of_intrinsic {f : ℕ}
    (h : ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.ExchangedModel (M.subgroupOf H) K f) :
    BorelReduction.SourceCases.ExchangedModel H M (K.map H.subtype) f := by
  rcases h with ⟨F,hF,hfin,hc,hf,hcard,hpair⟩ | ⟨m,hm,hf,hpair⟩
  · exact Or.inl ⟨F,hF,hfin,hc,hf,hcard,modelBorelPair_of_intrinsic hpair⟩
  · exact Or.inr ⟨m,hm,hf,modelBorelPair_of_intrinsic hpair⟩

variable [Finite G]

/-- The component overlap in H/O₂(H) is a Sylow normalizer, with all maps
provided by the original source kernel equality and marking. -/
theorem local_overlap_normalizer {f : ℕ}
    (hker : ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.sourceKernel (M.subgroupOf H) = pCore 2 H)
    (h : ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.ExchangedModel (M.subgroupOf H) K f) :
    ∃ P : Sylow 2 (actorImage H (K.map H.subtype)),
      normalizer (P : Set (actorImage H (K.map H.subtype))) =
        (actorImage H (M ⊓ K.map H.subtype)).subgroupOf (actorImage H (K.map H.subtype)) := by
  exact exists_sylow_normalizer_of_equiv (localComponentToSource hker) _ _
    (localComponentToSource_overlap hker)
    (BorelMarkings.source_overlap_normalizer (exchangedModel_of_intrinsic h))

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Exchanged
