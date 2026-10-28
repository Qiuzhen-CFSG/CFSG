module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.Reduction
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.Source
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.CenterAction.Torus

/-!
# Reduction of the higher E6 center action to matrix representation facts

The torus calculation identifies a central six-node value with an explicit
central coroot word. Its cube is therefore one. To transport the computed
diagram value from that coroot word to the original word, the diagram must
preserve the literal evaluation kernel. That premise is retained explicitly;
equality of matrix values alone would not justify the transport.

The two conclusions below have the exact shape consumed by
`centralCharacterComparison_of_central_kernel` in `CentralCharacters`.
Their torus-placement and diagram-kernel premises remain independent
representation obligations, including in characteristic three. This leaf
makes no unconditional assertion about arbitrary central words and imports
neither that consumer nor the WordKernels umbrella.

Sources: GLS3 §§1.12.5–6 and 2.5–2.6 (`refs/KGroup/GLS3/Chapter1.tex` and
`refs/KGroup/GLS3/chapter2.tex`), for the exceptional embeddings in
Aschbacher–Smith A.2.17, printed p.39.
-/

@[expose] public section
noncomputable section
open Theory.AlgebraicGroup.StandardRootSystem
namespace TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction

attribute [local instance] Classical.decEq
local instance : Fintype typeE7Roots := Fintype.ofFinite _
local instance : Fintype typeE8Roots := Fintype.ofFinite _

variable (F : Type*) [Field F]

omit [Field F] in
private theorem diagram_eval_eq_of_ker_le {G : Type*} [Group G]
    (v : SixNodeWord F →* G)
    (h : v.ker ≤ (v.comp (diagramWord F)).ker)
    {w z : SixNodeWord F} (he : v w = v z) :
    v (diagramWord F w) = v (diagramWord F z) := by
  have h0 : w * z⁻¹ ∈ v.ker := by
    simp only [MonoidHom.mem_ker, map_mul, map_inv, he, mul_inv_cancel]
  have hd := h h0
  change v (diagramWord F (w * z⁻¹)) = 1 at hd
  simpa only [map_mul, map_inv, mul_inv_eq_one] using hd

/-- The E7 center-action premise, reduced to torus placement and diagram relation preservation. -/
theorem e7Six_centerAction_of_torus (w : SixNodeWord F)
    (hc : ∀ z, Commute (e7Six F w) (e7Six F z))
    (ht : ∃ t : Fin 6 → Fˣ, (e7Six F w).val = sixCorootMatrix F e7Node t)
    (hd : (e7Six F).ker ≤ ((e7Six F).comp (diagramWord F)).ker) :
    e7Six F w ^ 3 = 1 ∧ e7Six F (diagramWord F w) = (e7Six F w)⁻¹ := by
  obtain ⟨t, ht⟩ := ht
  obtain ⟨u, hu, he⟩ := e7Six_eq_centralWord_of_torus F w hc t ht
  constructor
  · rw [he]
    exact e7Six_centralWord_cube F u hu
  · rw [diagram_eval_eq_of_ker_le F (e7Six F) hd he,
      e7Six_diagram_centralWord F u hu, he]

/-- The E8 center-action premise, reduced to torus placement and diagram relation preservation. -/
theorem e8Six_centerAction_of_torus (w : SixNodeWord F)
    (hc : ∀ z, Commute (e8Six F w) (e8Six F z))
    (ht : ∃ t : Fin 6 → Fˣ, (e8Six F w).val = sixCorootMatrix F e8Node t)
    (hd : (e8Six F).ker ≤ ((e8Six F).comp (diagramWord F)).ker) :
    e8Six F w ^ 3 = 1 ∧ e8Six F (diagramWord F w) = (e8Six F w)⁻¹ := by
  obtain ⟨t, ht⟩ := ht
  obtain ⟨u, hu, he⟩ := e8Six_eq_centralWord_of_torus F w hc t ht
  constructor
  · rw [he]
    exact e8Six_centralWord_cube F u hu
  · rw [diagram_eval_eq_of_ker_le F (e8Six F) hd he,
      e8Six_diagram_centralWord F u hu, he]


end TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction
