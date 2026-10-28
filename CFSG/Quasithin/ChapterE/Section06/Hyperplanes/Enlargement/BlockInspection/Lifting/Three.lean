module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Inputs
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.LocalFacts
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Obligations
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Setup
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Placement
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Detection

/-!
# Solvable A₃ lifting through corank-two centralizers

An A₃ block cannot be inserted into the perfect family in 1.2.3. Instead,
this module constructs a characteristic-two intermediate group from the
centralizer of the layer of C_G(A), together with the actual common Sylow Q.
Blocks constructed in that intermediate group lift back to C_G(A) by their
two-perfection and a relative subnormal chain through the normal layer
centralizer.

The final theorem discharges both layer placement and envelope block detection.
Its explicit earlier inputs are hyperplane characteristic two, exact E.6.7
and E.6.8, the exclusions E.6.18 and E.6.21, exact C.1.9, and the component
orbit clause of 1.2.1(3). No placement, block persistence or marked-model
premise remains. Hypothesis E.6.15 is unnecessary once these earlier source
conclusions are supplied.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.23,
printed pp.254–255 (PDF pp.265–266), and 1.2.3–4, printed p.505.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting
open ComponentBalance Three

variable {G : Type*} [Group G] [Finite G] {M V : Subgroup G}

/-- Conditional assembly of the independent localization and detection
obligations. The final theorem below supplies both from earlier source inputs. -/
theorem threeBlockLifting_of_layerPlacement_and_envelopeDetection
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    (placement : LayerPlacement M V)
    (detection : EnvelopeBlockDetection (sylowCentralizer (T : Subgroup G) V) M V) :
    ThreeBlockLifting M V := by
  intro U hU hUh L hL h3 he A hA hAU hc
  rcases placement U hU hUh L hL h3 he A hA hAU hc with hLC | ⟨X, hLX, hX⟩
  · obtain ⟨X, hLX, hXR, hb, ht⟩ := detection U hU hUh L hL h3 he A hA hAU hc hLC
    have hQH := (Chapter1.isSylowIn_iff.mp (h.sylow_obstruction hA)).2.1
    exact ⟨X, hLX, Or.inl ⟨⟨hXR.trans (layerEnvelope_le hQH),
      block_lift_from_layerEnvelope hQH (T.isPGroup'.to_le inf_le_left) hXR hb⟩, ht⟩⟩
  · exact ⟨X, hLX, Or.inr hX⟩

/-- The solvable A₃ lifting step in E.6.23, repaired independently of the
perfect local family in 1.2.3. Every new placement and block-construction
obligation is discharged. The output retains subnormality relative to C_G(A)
and the actual chi-zero module, or an ordinary component of that centralizer.
Only the permitted earlier source conclusions remain explicit. -/
theorem threeBlockLifting
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    (hchar : ∀ W : Subgroup G, IsHyperplane V W →
      generalizedFitting (centralizer (W : Set G)) = pCore 2 (centralizer (W : Set G)))
    (h67 : InvariantSubspaces.BlockSelection.E67Input T M V)
    (h8 : OddObstruction.EarlierComponentAlternatives M V
      (sylowCentralizer (T : Subgroup G) V))
    (h18 : SevenExcluded M V) (h21 : OddCoreFree V)
    (h19 : BlockCommutationInput G)
    (horbit : Three.Placement.EarlierComponentOrbits (G := G)) :
    ThreeBlockLifting M V :=
  threeBlockLifting_of_layerPlacement_and_envelopeDetection h
    (layerPlacement h hchar h8 h18 h21 horbit)
    (envelopeBlockDetection h h67 h19 h21 hchar)

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting
