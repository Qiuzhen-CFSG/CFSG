module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Representative
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldModels
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.Setup
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.QuotientCentralizer
public import CFSG.Quasithin.ChapterA.Section02.Statements
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.GroupTheory.PerfectCentralCover

/-!
# Source-classification preparation for the selected field component

The selected ordinary component is intrinsically quasisimple. Its quotient by
its full center is simple, nonabelian and semisimple. The universal Theorem A
therefore passes strong quasithinness to that section, and Theorem C gives its
complete model list with all parameters and actual model isomorphisms intact.

Only the precise universal earlier theorems are parameters here. Their local
hypotheses are proved from the selected component. Reducing the full list using
the PSL₃(2) centralizer component, and identifying the exceptional SL₃ covers
modulo the two-core, remain open. No three-model or odd-center alternative is
asserted by these preparation lemmas.

Source: Aschbacher--Smith, combined 1 March 2004 manuscript, proof of 15.3.38,
printed p.1137; Theorems A and C, p.33; A.3.6, pp.43--45; A.3.18, pp.51--52.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification
universe u
/-- The intrinsic simple-group input to the model sieve. Rank two is essential:
PSL₂(49) has a field involution with fixed component PSL₂(7), but has three-rank one. -/
structure SimpleInput (S : Type u) [Group S] where
  simple : IsSimpleGroup S
  nonabelian : ¬ IsMulCommutative S
  sqtk : IsSQTK CFSG.KnownSimple.IsKnownSimple S
  rank : primeRank 3 S = 2
  involution : MulAut S
  involution_order : orderOf involution = 2
  component : Subgroup involution.fixedSubgroup
  isComponent : IsComponent involution.fixedSubgroup component
  equiv : component ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)

variable {G : Type u} [Group G] {H K : Subgroup G} {v : G} (d : Input H K v)
include d

open ChapterA.Section02

/-- The central quotient is a genuine semisimple section, as required by Theorem A. -/
theorem Input.centralQuotient_semisimple : IsSemisimple (K ⧸ center K) := by
  let : IsQuasisimple K := d.quasisimple
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : IsQuasisimple (K ⧸ center K) := IsQuasisimple.of_surjective
    (QuotientGroup.mk' (center K)) (QuotientGroup.mk'_surjective _)
  let : IsQuasisimple (⊤ : Subgroup (K ⧸ center K)) :=
    IsQuasisimple.of_mulEquiv topEquiv.symm
  apply top_unique
  exact le_sSup (show IsComponent (K ⧸ center K) ⊤ from
    ⟨IsSubnormal.top, inferInstance⟩)

/-- Apply the complete universal Theorem A contract to the actual semisimple
section K/Z(K). This does not assume arbitrary quotient inheritance of rank. -/
theorem Input.centralQuotient_sqtk [Finite G]
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      TheoremA CFSG.KnownSimple.IsKnownSimple X) :
    IsSQTK CFSG.KnownSimple.IsKnownSimple (K ⧸ center K) := by
  have hK := d.component_sqtk
  exact ⟨(hA K).stronglyQuasithin_section hK.stronglyQuasithin hK.isKGroup
    (IsSectionOf.of_surjective (QuotientGroup.mk' (center K))
      (QuotientGroup.mk'_surjective _)) d.centralQuotient_semisimple,
    hK.isKGroup.quotient _⟩

/-- Rank two survives in the central quotient. If the quotient had rank at
most one, its Sylow three-groups would be cyclic. Perfect central transfer
then makes the Sylow three-groups upstairs cyclic as well, contradicting rank two. -/
theorem Input.centralQuotient_rank_ge [Finite G] :
    2 ≤ primeRank 3 (K ⧸ center K) := by
  by_contra hr
  have hr : primeRank 3 (K ⧸ center K) ≤ 1 := by omega
  let : IsQuasisimple K := d.quasisimple
  let P : Sylow 3 K := Classical.choice inferInstance
  let q := QuotientGroup.mk' (center K)
  have hc := (P.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)).isCyclic_of_odd_of_primeRank_le_one
    (by decide) hr
  have hP := PerfectCentralCovering.isCyclic_sylow_of_isCyclic_mapSurjective P q
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']) hc
  have := P.primeRank_le_one_of_isCyclic hP
  rw [d.rank] at this
  omega

/-- Theorem A supplies the matching upper bound on the actual central quotient. -/
theorem Input.centralQuotient_rank [Finite G]
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      TheoremA CFSG.KnownSimple.IsKnownSimple X) :
    primeRank 3 (K ⧸ center K) = 2 :=
  le_antisymm ((d.centralQuotient_sqtk hA).stronglyQuasithin 3 (by decide) (by decide))
    d.centralQuotient_rank_ge

/-- All simple-group sieve hypotheses follow from the selected component.
The ordinary fixed component, its actual isomorphism, and rank two are retained. -/
theorem Input.exists_simpleInput [Finite G]
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      TheoremA CFSG.KnownSimple.IsKnownSimple X) :
    Nonempty (SimpleInput (K ⧸ center K)) := by
  let : IsQuasisimple K := d.quasisimple
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : IsQuasisimple (K ⧸ center K) := IsQuasisimple.of_surjective
    (QuotientGroup.mk' (center K)) (QuotientGroup.mk'_surjective _)
  obtain ⟨D, hD, ⟨e⟩⟩ := d.exists_centralQuotient_fixed_component
  exact ⟨{
    simple := IsQuasisimple.simple
    nonabelian := Group.IsPerfect.not_isMulCommutative _
    sqtk := d.centralQuotient_sqtk hA
    rank := d.centralQuotient_rank hA
    involution := d.centralQuotientInvolutionAction
    involution_order := d.centralQuotientInvolutionAction_order
    component := D
    isComponent := hD
    equiv := e }⟩

/-- The universal Theorems A and C give the complete source model list.
Theorem A retains its quasithin K-group, semisimple-section and odd-prime
premises; Theorem C retains simplicity, nonabelianness, SQT and K. All local
instances of those premises are discharged here. The involution-centralizer
model sieve remains a separate obligation. -/
theorem Input.centralQuotient_theoremC [Finite G]
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      TheoremA CFSG.KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      TheoremC CFSG.KnownSimple.IsKnownSimple X) :
    IsTheoremCModel (K ⧸ center K) := by
  let : IsQuasisimple K := d.quasisimple
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  have hQ := d.centralQuotient_sqtk hA
  exact hC _ inferInstance (Group.IsPerfect.not_isMulCommutative _)
    hQ.stronglyQuasithin hQ.isKGroup

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification
