module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.Escape.Geometry

/-!
# The literal escaping-subgroup alternatives

These interfaces retain the subgroup, its relative normality, its action
on Ω₁Z(T), and its actual two-core quotient. The component construction
supplies a witness whenever there is an outside C-component. Constructing
a witness when all C-components lie in the common normalizer is the
independent theta-subgroup argument of 13.1.6.

The source application below proves the commuting geometry in the
component branch. The odd-prime commutator calculation and the later
three-rank refinement remain distinct obligations; this module does not
assert the complete existence theorem.
Source: Aschbacher--Smith 13.1.6 and 13.1.9, printed pp.868--870.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.Escape
open Chapter1 Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- The genuine odd-prime alternative, with O²(Y)=Y and the literal
quotient Y/O₂(Y). Exponent is exactly d. -/
def OddShape (Y : Subgroup G) : Prop :=
  IsPPerfect 2 Y ∧ ∃ d : ℕ, d.Prime ∧ Odd d ∧
    IsPGroup d (XiQuotient Y) ∧ Monoid.exponent (XiQuotient Y) = d ∧
      Group.nilpotencyClass (XiQuotient Y) ≤ 2

/-- A witness for source 13.1.6, with normality relative to the selected
maximal two-local H. The two alternatives share the same moving Y. -/
structure Witness (T : Sylow 2 G) (L H Y : Subgroup G) : Prop where
  le_overgroup : Y ≤ H
  normal : (Y.subgroupOf H).Normal
  outside : ¬ Y ≤ normalizer (L : Set G)
  moves : ⁅omegaOneCenterAmbient (T : Subgroup G),Y⁆ ≠ ⊥
  alternatives : OddShape Y ∨
    Y ∈ cComponentsIn H ∧ IsQuasisimple (XiQuotient Y) ∧ FaithfulMaximalLocal T Y

/-- The completed component construction gives the literal source witness.
The earlier canonical stars and 13.1.2 invariance/rigidity stay explicit. -/
theorem witness_of_outside_component
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hs : CanonicalStars T) (hrig : QuasisimpleRigidity T)
    {L H Y : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hH : IsMaximalTwoLocal H) (hTH : (T : Subgroup G) ≤ H)
    (hY : Y ∈ cComponentsIn H) (hout : ¬ Y ≤ normalizer (L : Set G)) :
    Witness T L H Y := by
  obtain ⟨hq,hN,hm,hf⟩ := escaping_component_of_stars h hmany hs hrig hL hn hH hTH hY hout
  exact ⟨hY.1,hN,hout,hm,Or.inr ⟨hY,hq,hf⟩⟩

/-- The actual first-paragraph p.870 consumer in the component branch,
with canonical geometry retained explicitly for its independent producer. -/
theorem component_witness_canonical_geometry
    (h : Hypothesis1311 T) (hrig : QuasisimpleRigidity T)
    {L H Y C : Subgroup G} (w : Witness T L H Y)
    (hH : H ∈ HOver G (T : Set G))
    (hY : Y ∈ cComponentsIn H) (hq : IsQuasisimple (XiQuotient Y))
    (hf : FaithfulMaximalLocal T Y) (hC : C ∈ cComponentsIn H)
    (hA : canonicalSupplement T L ∈ Chapter1.L G (T : Subgroup G))
    (hAC : canonicalSupplement T L ≤ C)
    (hTA : (T : Subgroup G) ≤ normalizer (canonicalSupplement T L : Set G))
    (hcore : (canonicalSupplement T L ⊔ (T : Subgroup G)).pCoreIn 2 =
      radicalSylowCentralizer T L)
    (hcent : radicalSylowCentralizer T (canonicalSupplement T L) = radicalSylowCentralizer T L) :
    ⁅Y,C⁆ ≤ Y.pCoreIn 2 ∧
      Y ≤ normalizer (canonicalSupplement T L : Set G) ∧
      Y.pCoreIn 2 ≤ radicalSylowCentralizer T L ∧
      IsSylowIn 2 (radicalSylowCentralizer T L) (Y ⊔ radicalSylowCentralizer T L) := by
  have hc := escaping_component_commutator h hrig hH hY hC hf hq w.outside hA hAC
  exact ⟨hc,sylow_join_of_canonical_centralizer hH.2 w.le_overgroup w.normal
    hAC hC.1 hTA hcore hcent hc⟩

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.Escape
