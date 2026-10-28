module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalOddNormalizer.JankoLargeCenterRadical
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalOddNormalizer.RudvalisCoverExclusion
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.CoverAssembly
/-!
# The original odd-actor deduction from the native four-local cover

The same component, radical and whole unitary module give the native
large-center radical and normal residual. The four-local cover then contradicts
all its possible placements. Applying this to the actual original escaping
component gives uniqueness of the odd-actor residual's maximal overgroup.
The sole additional input is the still-unproved uniform native cover; these
are conditional deductions, not unconditional source theorem claims.

Source: Aschbacher--Smith 4.2.13 and 13.3.16, with Kleidman--Wilson (1988),
Section 2, pp.488--493. Relative Sylow placement and all earlier inputs are retained.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup Theory.GroupTheory Chapter4 Chapter4.Section04 ChapterE
open Chapter4.Section02.Unitary OriginalPlaneCentralizers Chapter12.Section02
open scoped Pointwise IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G]
section Component
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The native cover is the only remaining input in the original J₄ contradiction. -/
theorem unitary_original_pushingUp_janko_false_of_cover
    (hnative : Janko4.LocalStructure.LargeCenterRadicals.MaximalTwoLocalCover)
    (s : Context T L V) {J H W : Subgroup G}
    (hcover : (L : Set G) ⊆ (J : Set G) * (L.pCoreIn 2 : Set G)) (hJH : J ≤ H)
    (hc : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H
      (H ⊓ normalizer (L : Set G))
      ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype)
      (J.pCoreIn 2) W)
    (K : Subgroup H) (hK : IsComponent H K) (e : K ⧸ center K ≃* Janko4.Model) : False := by
  obtain ⟨hP,hlarge,_,hn,⟨b⟩⟩ :=
    unitary_original_pushingUp_janko_radical s hcover hJH hc K hK e
  let := hn
  exact Janko4.LocalStructure.LargeCenterRadicals.unitary_radical_false_of_cover
    hnative _ hP hlarge _ b

end Component

section OriginalFlag
variable (D : ChapterF.Section09.Setup G) [IsElementaryAbelian 2 D.V]
  (s : Context D.T D.L D.V)
  (earlier : Theorem12213 KnownSimple.IsKnownSimple.{u})
  (hUV : D.Vplus ≤ D.V) (hZV : D.V₁ ≤ D.V)
  (hTZ : (D.T : Subgroup G) ≤ normalizer (D.V₁ : Set G))
  (hTU : (D.T : Subgroup G) ≤ normalizer (D.Vplus : Set G))
  (hZ : Nat.card D.V₁ = 2) (hU : Nat.card D.Vplus = 8)
  (B : Subgroup G) (hBV : B ≤ D.V)
  (hTB : (D.T : Subgroup G) ≤ normalizer (B : Set G)) (hB : Nat.card B = 4)
  (hHfull : D.H = normalizer (D.V₁ : Set G))
  (h1332 : Noncentrality.SupercriticalSource.Source1332OneTwo D.T)
  (fixed : OriginalFixedModule1332At D.T D.L)
  (five : OriginalAlternatingFiveModules1332At D.T D.L)

include s earlier hUV hZV hTZ hTU hZ hU hBV hTB hB hHfull h1332 fixed five

/-- Apply the conditional J₄ exclusion to the actual original odd-actor witness,
retaining the source's relative Sylow, full module and previous hypotheses. -/
theorem unitary_original_oddActorResidual_unique_of_janko_cover
    (hnative : Janko4.LocalStructure.LargeCenterRadicals.MaximalTwoLocalCover)
    (A : Subgroup G) (hAN : A ≤ normalizer (D.L : Set G))
    (hcomm : ⁅A,D.L⁆ ≤ D.L.pCoreIn 2) (hodd : Odd (Nat.card A))
    (hAV : A ≤ centralizer (D.V : Set G)) :
    UniqueMaximalOvergroup (oddActorResidual D.L A) (normalizer (D.L : Set G)) := by
  by_contra hnot
  obtain ⟨J,H,S,c,hpush,_,hJH,_,hc,_,_,K,hK,_,⟨e⟩⟩ :=
    unitary_original_oddActorResidual_janko_only D s earlier hUV hZV hTZ hTU hZ hU
      B hBV hTB hB hHfull h1332 fixed five A hAN hcomm hodd hAV hnot
  have hcover : (D.L : Set G) ⊆ (J : Set G) * (D.L.pCoreIn 2 : Set G) := by
    have h12 := unitary_original_hypothesis1223 s.hypothesis s.maximal s.quotient
    obtain ⟨hcover,_,_,_⟩ := chosen_oddActorResidual_cover h12.toHypothesis1221 s.chosen
      A hAN hcomm hodd hAV
    have hi : oddActorResidual D.L A ≤ J :=
      ((le_inf le_rfl ((oddActorResidual_le D.L A).trans inf_le_left)).trans hpush.2).trans
        inf_le_left
    exact hcover.subset.trans (Set.mul_subset_mul hi Set.Subset.rfl)
  exact unitary_original_pushingUp_janko_false_of_cover hnative s hcover hJH hc K hK e

end OriginalFlag
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
