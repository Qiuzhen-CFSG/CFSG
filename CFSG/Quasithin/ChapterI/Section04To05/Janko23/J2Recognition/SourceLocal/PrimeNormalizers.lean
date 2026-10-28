module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.EdgeCentralizer
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.EdgeApplication
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal

/-!
# Prime-local calculations for the source J₂ graph

This assembles 47.2–47.3 from the order and marked involution geometry of
47.1. The five-local proof supplies both actual conjugacy classes, their
marked normalizers and components, and the elementary self-centralizing
Sylow five with its D₁₂ complement. Those conclusions discharge every
five-local input to the three-local proof, including the perfect central
cover, the genuine PGL₂(9) quotient, and the marked Sylow-three action.

The quotient uses X as a normal subgroup of its normalizer. Its extension
identification uses an actual order-eight element, avoiding the erroneous
printed semidihedral assertion. The seven-local argument likewise does
not use the printed order-21 assertion in 47.4.

The direct 47.10 applications identify the literal edge centralizer
`F.K = C_G(F.B)` with A₅, retain both endpoint inclusions, and prove the
proper-overgroup premise of `SourceLocal.localDataOfCalculations`. The
47.5 representative construction also supplies the A₅ edge-fixer input.

Only the earlier order and `SelectedGeometry` remain conditional. Their
producer is `qt-i47-j2-source-involutions`; the final graph assembly owner
`qt-i47-j2-local-graph-geometry` must discharge them. No prime-local or
proper-overgroup conclusion is assumed here.

Source: Aschbacher, *Sporadic Groups* (1994), pp.261–262 and 266.
-/

public section

open Subgroup Theory.GroupTheory.GraphUniquenessSystem

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers

variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] {D : Seed G}

/-- Both complete prime-local source families, conditional only on the exact
earlier order and selected involution geometry of 47.1. In particular the
five-local input of the three-local theorem is discharged here. -/
theorem source_prime_local_of_selectedGeometry (hG : Nat.card G = 604800)
    (S : InvolutionGeometry.SelectedGeometry D) :
    FiveLocal.SourceConclusion D S.t ∧ ThreeLocal.SourceConclusion D := by
  have hfive := FiveLocal.sourceConclusion_of_selectedGeometry hG S
  exact ⟨hfive, ThreeLocal.sourceConclusion_of_source hG S hfive⟩

/-- Keep the actual covering map and normalizer actors available to later
source consumers, without asking them to assume the five-local theorem. -/
theorem centralizerCalculation_of_selectedGeometry (hG : Nat.card G = 604800)
    (S : InvolutionGeometry.SelectedGeometry D) :
    Nonempty (ThreeLocal.CentralizerCalculation D) :=
  ThreeLocal.centralizerCalculation_of_source hG S
    (FiveLocal.sourceConclusion_of_selectedGeometry hG S)

/-- Every proper intermediate subgroup above an actual A₅ in N_G(X)
lies in C_G(X). All local recognition and quotient-compatibility premises
of the projective overgroup calculation are discharged. -/
theorem proper_overgroup_le_centralizer_of_selectedGeometry
    (hG : Nat.card G = 604800) (S : InvolutionGeometry.SelectedGeometry D)
    (F U : Subgroup G) (he : Nonempty (F ≃* alternatingGroup (Fin 5)))
    (hFM : F ≤ normalizer (D.X : Set G)) (hFU : F ≤ U)
    (hUM : U ≤ normalizer (D.X : Set G)) (hU : U ≠ normalizer (D.X : Set G)) :
    U ≤ centralizer (D.X : Set G) := by
  obtain ⟨H⟩ := centralizerCalculation_of_selectedGeometry hG S
  exact H.proper_overgroup_le_centralizer F U he hFM hFU hUM hU

/-- The exact `hovergroups` quantifiers of `SourceLocal.localDataOfCalculations`,
for its literal pointwise edge fixer. -/
theorem edgeFrame_proper_overgroups_of_selectedGeometry
    (hG : Nat.card G = 604800) (S : InvolutionGeometry.SelectedGeometry D)
    (F : EdgeFrame D)
    (he : Nonempty (edgeFixer G D.base F.y ≃* alternatingGroup (Fin 5))) :
    ∀ U : Subgroup G, edgeFixer G D.base F.y ≤ U →
      U ≤ normalizer (D.X : Set G) → U ≠ normalizer (D.X : Set G) →
      U ≤ centralizer (D.X : Set G) := by
  obtain ⟨H⟩ := centralizerCalculation_of_selectedGeometry hG S
  exact Overgroups.edgeFrame_proper_overgroups F he H.perfect H.normalizerQuotientEquiv
    (H.projective_centralizer_image H.normalizerQuotientEquiv)

/-- All prime-local inputs of the source 47.5 representatives are supplied
by 47.2–47.3, including both normalizer orders and the Sylow-three action. -/
theorem threePairRepresentatives_of_selectedGeometry (hG : Nat.card G = 604800)
    (S : InvolutionGeometry.SelectedGeometry D) : Nonempty (ThreePairRepresentatives D) := by
  obtain ⟨hfive, hthree⟩ := source_prime_local_of_selectedGeometry hG S
  exact Representatives.threePairRepresentatives_nonempty S hfive.root hfive.twoCentral
    hthree.sylow hthree.normalizer_card hthree.local_normalizer_card

/-- The four suborbits used by the graph assembly, with no prime-local or
representative premise left. -/
theorem fourSuborbits_of_selectedGeometry (hG : Nat.card G = 604800)
    (S : InvolutionGeometry.SelectedGeometry D) : FourSuborbits D := by
  obtain ⟨R⟩ := threePairRepresentatives_of_selectedGeometry hG S
  exact R.fourSuborbits hG (source_prime_local_of_selectedGeometry hG S).2.normalizer_card

/-- The A₅ pointwise fixer is obtained for every actual edge at the base. -/
theorem edgeFixer_equiv_of_selectedGeometry (hG : Nat.card G = 604800)
    (S : InvolutionGeometry.SelectedGeometry D)
    {Y : D.Vertex} (hY : D.graph.Adj D.base Y) :
    Nonempty (edgeFixer G D.base Y ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨R⟩ := threePairRepresentatives_of_selectedGeometry hG S
  exact R.edgeFixer_equiv hG
    (source_prime_local_of_selectedGeometry hG S).2.normalizer_card hY

/-- Both direct 47.10 consumers on the same actual frame. This also
discharges the A₅ edge-fixer premise using the source 47.5 construction.
The centralizer and endpoint inclusions are literal ambient subgroups. -/
theorem edgeFrame_calculations_of_selectedGeometry (hG : Nat.card G = 604800)
    (S : InvolutionGeometry.SelectedGeometry D) (F : EdgeFrame D) :
    Nonempty (F.K ≃* alternatingGroup (Fin 5)) ∧
    D.X ⊔ F.y.val ≤ F.K ∧
    (∀ U : Subgroup G, edgeFixer G D.base F.y ≤ U →
      U ≤ normalizer (D.X : Set G) → U ≠ normalizer (D.X : Set G) →
      U ≤ centralizer (D.X : Set G)) := by
  have he := edgeFixer_equiv_of_selectedGeometry hG S F.adjacent
  exact ⟨FiveLocal.edgeFrame_centralizer_equiv_of_selectedGeometry hG S F he,
    F.endpoints_le he, edgeFrame_proper_overgroups_of_selectedGeometry hG S F he⟩

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers
