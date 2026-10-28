module
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.AxisAlignment.Coordinates
public import CFSG.Quasithin.Chapter10.SourceA5OriginalPairConsumer
public import CFSG.Quasithin.Chapter10.SourceA5EscapingOrthogonalAction

/-!
# The original escaping A₅ action gives a strict overcomponent

The escaping Baumann normalizer forces a nontrivial source fixed center and
supplies the original orthogonal action. The prescribed original layer vectors
admit compatible opposite-plane coordinates. The marked component theorem and
original second-block cubic exclusion then produce a strict overcomponent
with no alternating-seven quotient. No coordinate, action or fixed-center
premise remains beyond the original Fundamental Setup, A₅ marking,
nonnormality and escaping-normalizer hypotheses.

Source: Aschbacher–Smith 10.2.1, printed p.743.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC FixedCenterOvercomponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- An escaping original A₅ Baumann normalizer produces a strict component
in the centralizer of the prescribed original second vector. All coordinates
and fixed-center premises are discharged from the original source input. -/
theorem source_a5_original_strict_component_not_seven
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal) :
    ∃ t : G, t∈(T : Subgroup G) ∧ t∉normalizer (L : Set G) ∧
      ∃ p : SourceA5OriginalFixedPair D t,
      ∃ I : Subgroup G, L<I ∧ I≤centralizer ({p.second} : Set G) ∧
        (I.subgroupOf (centralizer ({p.second} : Set G))).IsCComponent ∧
        centralizer ({p.second} : Set G)≤normalizer (I : Set G) ∧
        ¬ Nonempty ((I ⧸ pCore 2 I) ≃* alternatingGroup (Fin 7)) := by
  have hne := source_a5_fixed_center_ne_bot_of_escape D e hn hout
  obtain ⟨t,ht,htn,hgen,⟨p⟩⟩ := source_a5_exists_original_fixed_pair D e hn hout
  obtain ⟨H,hH,hHN,hWE,hred,g,hg,hresq,S,hS,hSM,hSA,hG6,hr,hclass,
    hP,hC,hM,hthree,hnot,d,hbinary,c,ew,hw,hA,hB⟩ :=
    source_exists_escaping_orthogonal_action D e hn hout
  let := hred.normal
  let := hred.elementary
  obtain ⟨c',ew',hw',u₁,u₂,a,b,ha,hb,hc₁,hc₂,hu₁,hu₂,_,_⟩ :=
    source_a5_original_pair_coordinates D e hn hne hout ht htn p hgen
      hH hWE hred S hSA hG6.faithful c ew hw
  exact ⟨t,ht,htn,p,source_a5_original_fixed_pair_strict_component_not_seven
    D e hn hout ht p hH hHN hred S c' ew' hw' u₁ u₂ a b ha hb hc₁ hc₂ hu₁ hu₂⟩

end CFSG.Quasithin.Chapter10
