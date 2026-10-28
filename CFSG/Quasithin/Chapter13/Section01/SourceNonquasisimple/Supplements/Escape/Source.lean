module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.Escape.Theta.Outside
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.Escape.Refinement.Source

/-!
# The escaping-subgroup source construction and its classification consumer

The theta construction and the outside-component construction give the
same source witness. The commutator bound then supplies canonical
normalization, core containment and the literal Sylow assertion. The
PSL₂ quotient forces three-rank one, refining the quotient alternatives.

Only authorized earlier inputs remain: canonical stars are constructed
by qt-d-1314-canonical-radical-star; canonical supplement geometry belongs
to qt-d-1317-supplements; earlier 13.1.2 classification and rigidity and
all final source premises are discharged by qt-d-1317-source.
Source: Aschbacher--Smith 13.1.6 and 13.1.9, printed pp.868--870.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.Escape
open Chapter1 Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- Every clause used after the first paragraph of p.870, on the same Y. -/
structure RefinedWitness (T : Sylow 2 G) (L H C Y : Subgroup G) : Prop where
  witness : Witness T L H Y
  commutator_le : ⁅Y,C⁆ ≤ Y.pCoreIn 2
  normalizes : Y ≤ normalizer (canonicalSupplement T L : Set G)
  core_le : Y.pCoreIn 2 ≤ radicalSylowCentralizer T L
  sylow : IsSylowIn 2 (radicalSylowCentralizer T L) (Y ⊔ radicalSylowCentralizer T L)
  threeRank : primeRank 3 Y ≤ 1
  refined : RefinedShape T H Y

/-- The complete escape construction and refinement, conditional only on
the specified earlier source statements and literal canonical geometry. -/
theorem exists_refined_witness (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hs : CanonicalStars T) (hrig : QuasisimpleRigidity T)
    (hclass : QuasisimpleClassification T) {L H C : Subgroup G}
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    (hH : IsMaximalTwoLocal H) (hTH : (T : Subgroup G) ≤ H)
    (hne : H ≠ normalizer (L : Set G))
    (hA : canonicalSupplement T L ∈ MainForward.faithfulLocalComponents T)
    (hC : C ∈ cComponentsIn H) (hAC : canonicalSupplement T L ≤ C)
    (hTA : (T : Subgroup G) ≤ normalizer (canonicalSupplement T L : Set G))
    (hcore : (canonicalSupplement T L ⊔ (T : Subgroup G)).pCoreIn 2 = radicalSylowCentralizer T L)
    (hcent : radicalSylowCentralizer T (canonicalSupplement T L) = radicalSylowCentralizer T L)
    {p : ℕ} (hmodel : ClassicalGroup.IsPSL (XiQuotient (canonicalSupplement T L)) 2 p) :
    ∃ Y : Subgroup G, RefinedWitness T L H C Y := by
  obtain ⟨Y,w⟩ := Theta.witness_exists_of_stars h hmany hs hrig hL hn hH hTH hne
  obtain ⟨hc,hN,hO,hS⟩ := witness_canonical_geometry h hmany hs hrig hL hn hH hTH hne
    w hA hC hAC hTA hcore hcent
  have hr := threeRank_le_one_of_canonical_commutator h hH (hAC.trans hC.1) w.le_overgroup
    hN ((commutator_mono le_rfl hAC).trans hc) hmodel
  exact ⟨Y,w,hc,hN,hO,hS,hr,w.refined hclass hr⟩

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.Escape

namespace CFSG.Quasithin.Chapter14.Section03.FaithfulSource
open Chapter1 Chapter12.Section02 Chapter13.Section01
open Chapter13.Section01.SourceNonquasisimple.Supplements
open Chapter13.Section01.SourceNonquasisimple.Supplements.Escape
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L₀ : Subgroup G}

/-- The literal 13.3.1 nonquasisimple counterexample supplies the maximal L
used by the escape construction. Geometry is retained at that same L.
The final source owner must discharge the stated earlier premises. -/
theorem Hypothesis1331.refined_escape_of_many (h : Hypothesis1331 T L₀)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ IsQuasisimple (XiQuotient L₀))
    (hs : CanonicalStars T) (hrig : QuasisimpleRigidity T)
    (hclass : QuasisimpleClassification T) :
    ∃ L : Subgroup G, L₀ ≤ L ∧ FaithfulMaximalLocal T L ∧
      ¬ IsQuasisimple (XiQuotient L) ∧
      ∀ H C : Subgroup G, IsMaximalTwoLocal H → (T : Subgroup G) ≤ H →
        H ≠ normalizer (L : Set G) →
        canonicalSupplement T L ∈ MainForward.faithfulLocalComponents T →
        C ∈ cComponentsIn H → canonicalSupplement T L ≤ C →
        (canonicalSupplement T L ⊔ (T : Subgroup G)).pCoreIn 2 = radicalSylowCentralizer T L →
        radicalSylowCentralizer T (canonicalSupplement T L) = radicalSylowCentralizer T L →
        ∀ p : ℕ, ClassicalGroup.IsPSL (XiQuotient (canonicalSupplement T L)) 2 p →
          ∃ Y : Subgroup G, RefinedWitness T L H C Y := by
  obtain ⟨L,_,hL₀,hL,hLn,_,_⟩ := h.maximal_counterexample_of_many hmany hn
  refine ⟨L,hL₀,hL,hLn.2,?_⟩
  intro H C hH hTH hne hA hC hAC hcore hcent p hmodel
  have hsetup := canonical_supplement_setup_source h.hypothesis1311 hL hLn.2
  exact exists_refined_witness h.hypothesis1311 hmany hs hrig hclass hL hLn.2 hH hTH hne
    hA hC hAC hsetup.2.2.2.1 hcore hcent hmodel

end CFSG.Quasithin.Chapter14.Section03.FaithfulSource
