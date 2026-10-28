module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.SourceSwapped
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.SourceContainment

/-!
# The original normal-or-component-containment dichotomy

The genuine supercritical/Fitting argument either makes X normal in H or
detects a noncentral ordinary component in H/O₂(H). Its lifted C-component
has a normal T-orbit. For a normal detected component, the complete normal
containment theorem applies; otherwise the exchanged-component theorem applies.
In both cases the original complement P and subgroup X lie in the same
component orbit, with the original detected component and quasisimple
intrinsic two-core quotient retained.

This proves the first half of the adequate intrinsic Proposition 1.3.4 from
its original LocalInput, SQTK and actual Sylow hypotheses, together with the
genuine earlier universal Theorems A and C. The subsequent four embedding
alternatives remain separate. Source: Aschbacher--Smith, pp.509--510.
-/

public section
namespace CFSG.Quasithin.Chapter1.XiEmbedding
open Subgroup Theory.GroupTheory
universe u
variable {G : Type u} [Group G] [Finite G]

theorem LocalInput.complement_and_X_le_detected_orbit
    (hA : ∀ (Y : Type u) [Group Y] [Finite Y],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple Y)
    (hC : ∀ (Y : Type u) [Group Y] [Finite Y],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple Y)
    {p : ℕ} {T X P H L : Subgroup G} (h : LocalInput p T X P H)
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (hT : IsSylowIn 2 T H)
    (hL : ComponentDetection P H L) :
    P ≤ componentOrbit L T ∧ X ≤ componentOrbit L T := by
  by_cases hn : (L.subgroupOf H).Normal
  · obtain ⟨hP,hX⟩ := h.complement_and_X_le_normal_component hA hC hH hL hn
    exact ⟨hP.trans (le_componentOrbit L T),hX.trans (le_componentOrbit L T)⟩
  · exact h.complement_and_X_le_swapped_orbit hA hC hH hT hL hn

/-- Original-source detection and both containments, with the detected orbit
normal in H and fully moved by the original complement. -/
theorem LocalInput.normal_or_detected_containment
    (hA : ∀ (Y : Type u) [Group Y] [Finite Y],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple Y)
    (hC : ∀ (Y : Type u) [Group Y] [Finite Y],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple Y)
    {p : ℕ} {T X P H : Subgroup G} (h : LocalInput p T X P H)
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (hT : IsSylowIn 2 T H) :
    (X.subgroupOf H).Normal ∨ ∃ L : Subgroup G,
      ComponentDetection P H L ∧ ((componentOrbit L T).subgroupOf H).Normal ∧
        ⁅componentOrbit L T,P⁆ = componentOrbit L T ∧
        P ≤ componentOrbit L T ∧ X ≤ componentOrbit L T := by
  rcases h.normal_or_detected_commutator_orbit hH hT with hn | ⟨L,hL,hn,hcomm⟩
  · exact Or.inl hn
  · exact Or.inr ⟨L,hL,hn,hcomm,h.complement_and_X_le_detected_orbit hA hC hH hT hL⟩

/-- The first half of adequate intrinsic 1.3.4, with no separate detection,
outer-action or containment input. -/
theorem LocalInput.normal_or_quasisimple_component_orbit
    (hA : ∀ (Y : Type u) [Group Y] [Finite Y],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple Y)
    (hC : ∀ (Y : Type u) [Group Y] [Finite Y],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple Y)
    {p : ℕ} {T X P H : Subgroup G} (h : LocalInput p T X P H)
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (hT : IsSylowIn 2 T H) :
    (X.subgroupOf H).Normal ∨ ∃ L : Subgroup G,
      L ∈ cComponentsIn H ∧ IsQuasisimple (XiQuotient L) ∧
        P ≤ componentOrbit L T ∧ X ≤ componentOrbit L T := by
  rcases h.normal_or_detected_containment hA hC hH hT with hn | ⟨L,hL,_,_,hP,hX⟩
  · exact Or.inl hn
  · exact Or.inr ⟨L,hL.mem,hL.quasisimple,hP,hX⟩

end CFSG.Quasithin.Chapter1.XiEmbedding
