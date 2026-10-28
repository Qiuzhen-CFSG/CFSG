module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction.Complete
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction.Generation
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction.LocalNormalizer

/-!
# The literal candidate-overgroup application of the FF setup

Apply the completed escape theorem to the actual maximal two-local H
containing L_R T. Canonical stars supply the original centralizer control;
the same Y then gives the escaping Thompson commutator K and the reduced
omega closure D. The reexported common-action theorem also constructs the
faithful conjugation representation, its marked PSL₂(p) factor and direct
product, and the binary fixed-codimension bound for the same Thompson actors.
The component and cubic branches give K = Y = [K,J] and an actual
nontrivial Thompson-family actor. On a marked irreducible product section,
Clifford theory constructs repeated coordinates and finite Schur theory
forces multiplicity greater than one. The section budget derives the FF
inequality and B.5 excludes the odd-prime-by-two section. The quotient maps
and relative normality belong to the original candidate. On a section moved
by the simple K-image, its kernel and the faithful radical action also give
zero rank loss for the same Thompson actor. In the component and cubic
branches, the common chief section is now constructed inside the literal
double moved subgroup, for the smaller group L_R K A, and the canonical
PSL₂(p) factor acts faithfully on it. In the larger odd-prime branch, the
actual moving actor has rank at most two, and the constructed prime-order
subgroup gives its own common chief section. Restricting that action to the
commuting product supplies the repeated coordinates and closes the odd-prime
FF exclusion. The candidate consequently has one of the actual A₅, L₃(2),
and cyclic-three quotients, with K = Y = [K,J]. Their actual maps identify
the K-image with Y/O₂(Y), so it is simple and the constructed common chief
section has zero rank loss. Perfectness of the canonical factor now forces
displacement at least three. The small-quotient automorphism rank bound then
forces j = 1, actor rank two, and displacement exactly three on the module
and section, excluding the cyclic-three quotient. Every nonidentity actor
element has the same fixed space, so the actual action is quadratic. The
denominator and the quotient above the section are fixed by both the actor
and the simple K-image. Sharp displacement also constructs exactly three
copies of an absolutely irreducible constituent of K̂Â. An actual external
tensor equivalence identifies the canonical factor with the full natural
SL₃(2) action on the multiplicity space. The original actor remains faithful
on the constituent and has rank two there. A faithful rank-two hyperplane
actor excludes the A₅ second factor. For the surviving SL₃(2) factor, its
outer group has order two, so a nontrivial inner actor involution and the
three-involution generation bound force natural degree three on that same
constituent. Thus both factors have actual natural tensor markings. The
actor image lies in the second-factor image under the literal chief-section
quotient map. In the same natural coordinates it is the full pointwise fixer
of its common plane, the two-core of the plane stabilizer. Triviality of
the simple factor's centralizer in the reduced KR-image lifts actor containment
to the original action on D. Every nontrivial member of the Thompson family
has the same sharp displacement. Comparing them on the original tensor
identifies all their images with the same common-axis four-group, and hence
the original Thompson subgroup has exactly that image. Its normalizer lifts
into N_G(L), and the whole moved module is the same nine-dimensional natural
tensor with zero chief-section denominator. The original radical image gives
the Sylow intersection used by the natural point parabolic. Its fixed-space
centralizer and the common-axis normalizer generate K under the literal
action map. Canonical centralizer uniqueness puts both generators in N_G(L),
contradicting escape.

The exact GLS G.26.18 normalizer product is now proved for the literal XR.
Failure of that product constructs the maximal normal kernel, its odd chief
section, the moving prime line and the original actor hyperplane. The
Frattini normalizer quotient has a self-centralizing odd minimal normal
section, retaining noncoverage by the original normalizer. The local envelope
obstruction closes this branch, and induction on proper Sylow overgroups
discharges the product premise. Choosing the original supported prime gives
j in {0,1} and completes the conditional candidate contradiction.

`candidate_false` and `supplement_candidate_false` from Complete.lean exclude the actual contrary overgroups;
Hypothesis1331.canonical_ff_exclusion_of_many applies this to the original
13.3.2 maximal counterexample. Only CanonicalStars, QuasisimpleRigidity and
QuasisimpleClassification remain explicit earlier-source inputs, with final
discharge owned by qt-d-1317-source. The supplement uniqueness and Thompson
movement assembly remains with qt-d-1317-supplements.
Source: Aschbacher--Smith 13.1.9, printed pp.869--871.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open CFSG.Quasithin ChapterB
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction
open Chapter1 Chapter1.Section02 Chapter12.Section02 ChapterA.Section04 Escape
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- Application to the actual outside maximal two-local. The earlier canonical
geometry constructs Y. This geometric interface retains its explicit index;
Complete.lean constructs that index and proves the final contradiction. -/
theorem candidate_commutator_geometry (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hs : CanonicalStars T) (hrig : QuasisimpleRigidity T)
    (hclass : QuasisimpleClassification T) {L H C : Subgroup G}
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    (hH : IsMaximalTwoLocal H) (hTH : (T : Subgroup G) ≤ H)
    (hne : H ≠ normalizer (L : Set G))
    (hA : canonicalSupplement T L ∈ MainForward.faithfulLocalComponents T)
    (hC : C ∈ cComponentsIn H) (hAC : canonicalSupplement T L ≤ C)
    (hcore : (canonicalSupplement T L ⊔ (T : Subgroup G)).pCoreIn 2 = radicalSylowCentralizer T L)
    (hcent : radicalSylowCentralizer T (canonicalSupplement T L) = radicalSylowCentralizer T L)
    {p : ℕ} (hmodel : ClassicalGroup.IsPSL (XiQuotient (canonicalSupplement T L)) 2 p)
    {j : ℕ}
    (hN : normalizer (thompsonJ (radicalSylowCentralizer T L) j : Set G) ≤
      normalizer (L : Set G)) :
    ∃ Y : Subgroup G, RefinedWitness T L H C Y ∧
      ¬ thompsonCommutator T L Y j ≤ Y.pCoreIn 2 ∧
      ¬ thompsonCommutator T L Y j ≤ normalizer (L : Set G) ∧
      ⁅omegaOneCenterAmbient (T : Subgroup G),thompsonCommutator T L Y j⁆ ≠ ⊥ ∧
      IsSylowIn 2 (radicalSylowCentralizer T L)
        (thompsonCommutator T L Y j ⊔ radicalSylowCentralizer T L) ∧
      ⁅canonicalSupplement T L,
        thompsonCommutator T L Y j ⊔ radicalSylowCentralizer T L⁆ ≤
        (canonicalSupplement T L).pCoreIn 2 ⊓
          (thompsonCommutator T L Y j ⊔ radicalSylowCentralizer T L).pCoreIn 2 ∧
      canonicalSupplement T L ⊔ (T : Subgroup G) ≤
        normalizer (omegaClosure T L Y j : Set G) ∧
      IsPReduced 2 ((omegaClosure T L Y j).subgroupOf
        (thompsonCommutator T L Y j ⊔ radicalSylowCentralizer T L)) ∧
      IsElementaryAbelian 2 (omegaClosure T L Y j) ∧
      omegaClosure T L Y j ≤ radicalSylowCentralizer T L := by
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  obtain ⟨Y,w⟩ := exists_refined_witness h hmany hs hrig hclass hL hn hH hTH hne
    hA hC hAC (sylow_normalizes_canonicalSupplement hTL) hcore hcent hmodel
  have hZ := (nonquasisimple_centralizer_unique_of_stars h hmany hs hL hn).2.1
  have he := thompson_commutator_escape w hTH hN hZ
  have hi := thompson_commutator_invariance w hTH (hAC.trans hC.1) hTL j
  have hD := omegaClosure_elementary_le_radical h w hH hTH (hAC.trans hC.1) hTL hcore j
  exact ⟨Y,w,he.2.1,he.2.2.1,he.2.2.2,hi.2.2.2.2,
    thompson_commutator_core_bound w hTH (hAC.trans hC.1) hAC hTL j,
    (omegaClosure_geometry w hTH (hAC.trans hC.1) hTL j).2.2.2,
    omegaClosure_reduced h w hH hTH (hAC.trans hC.1) hTL hcore j,hD.1,hD.2⟩
end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction
