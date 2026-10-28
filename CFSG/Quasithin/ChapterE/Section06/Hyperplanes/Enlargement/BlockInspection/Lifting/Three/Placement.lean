module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Setup
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Placement.Contracts
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Placement.Borel
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Placement.Symplectic

/-!
# Assembly of solvable block placement from two component-action branches

Failure to centralize E(C_G(A)) detects an ordinary component X. The earlier
source results restrict X to the Borel or symplectic family, with fixed space
exactly A. A containing-or-commuting theorem for the corresponding family
then places the original block in X.

The final theorem supplies both proved mixed-component action branches.
Its only explicit earlier inputs are hyperplane characteristic two, the
complete E.6.8 alternatives, E.6.18, E.6.21 and the orbit clause of 1.2.1(3).
E.6.15 is not needed once these earlier conclusions are available. The
component alternative retains ordinary quasisimplicity and subnormality
relative to C_G(A); the other alternative uses the actual embedded
centralizer C_{C_G(A)}(E(C_G(A))).

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the solvable
branch of E.6.23, printed pp.254–255 (PDF pp.265–266).
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three
open ComponentBalance Placement

variable {G : Type*} [Group G] [Finite G] {M V : Subgroup G}

/-- Conditional assembly from the two independent mixed-component branches.
Neither branch is being asserted as an earlier source theorem. -/
theorem layerPlacement_of_component_interactions [IsElementaryAbelian 2 V]
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    (hchar : ∀ W : Subgroup G, IsHyperplane V W →
      generalizedFitting (centralizer (W : Set G)) = pCore 2 (centralizer (W : Set G)))
    (h8 : OddObstruction.EarlierComponentAlternatives M V
      (sylowCentralizer (T : Subgroup G) V))
    (h18 : SevenExcluded M V) (h21 : OddCoreFree V)
    (hb : BorelInteraction M V) (hs : SymplecticInteraction M V) :
    LayerPlacement M V := by
  classical
  intro U hU hUh L hL h3 he A hA hAU hc
  by_cases hLC : L ≤ layerKernel (centralizer (A : Set G))
  · exact Or.inl hLC
  · obtain ⟨X, hX, hnc⟩ := exists_noncommuting_component
      (hL.1.trans (Subgroup.centralizer_le hAU)) hLC
    obtain ⟨hf, hm⟩ := component_models h hchar h8 h18 h21 hA hc hX
    have hLX : L ≤ X ∨ ⁅L, X⁆ = ⊥ := by
      rcases hm with b | s
      · exact hb U hU hUh L hL h3 he A hA hAU hc X hX hf b
      · exact hs U hU hUh L hL h3 he A hA hAU hc X hX hf s
    exact Or.inr ⟨X, hLX.resolve_right hnc, hX⟩

/-- The solvable A₃ block centralizes the ordinary layer of C_G(A), or lies
in one of its ordinary components. Both mixed-component action obligations
are discharged; all remaining explicit inputs are permitted earlier source
results. No identification of the block with A₄ is assumed. -/
theorem layerPlacement
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    (hchar : ∀ W : Subgroup G, IsHyperplane V W →
      generalizedFitting (centralizer (W : Set G)) = pCore 2 (centralizer (W : Set G)))
    (h8 : OddObstruction.EarlierComponentAlternatives M V
      (sylowCentralizer (T : Subgroup G) V))
    (h18 : SevenExcluded M V) (h21 : OddCoreFree V)
    (horbit : EarlierComponentOrbits (G := G)) : LayerPlacement M V := by
  let := h.elementary
  exact layerPlacement_of_component_interactions h hchar h8 h18 h21
    (borelInteraction h) (symplecticInteraction h hchar horbit)

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three
